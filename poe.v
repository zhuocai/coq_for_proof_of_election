Require Import List.
Require Import PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Lia. 
Require Import Coq.Arith.Arith. 
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Lia.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Lists.ListDec.
Require Import Coq.Lists.ListSet. 
Scheme Equality for list. 
Import ListNotations.

Section ProofOfElection. 

Definition node:=nat.
Definition slot:=nat.
Variable nodes: set node. 
Definition n_nodes: nat:= length nodes.
Variable n_faulty:nat.
Definition n_committee: nat:= 2*n_faulty + 1.
Variable local_committees: node->slot->set node. 
Variable is_honest_bool: node->bool.
Definition is_honest (n:node):Prop
    := is_honest_bool n = true.

Variable local_committee_leader_order: node->slot->node->nat. 
Variable local_committee_leaders: node->slot->nat->node. 


Definition node_eq_dec := Nat.eq_dec.

Definition in_nodeset_bool (n:node) (nodes:set node):bool:=
    set_mem node_eq_dec n nodes.

Lemma set_mem_iff_list_in: 
    forall n:node, forall setx: set node,
    set_mem node_eq_dec n setx = true <-> In n setx.
    intros.
    split.
    - apply set_mem_correct1.
    - apply set_mem_correct2.
Qed.

Hypothesis committee_size: forall s:slot, forall n:node, 
    length (local_committees n s) = n_committee.

Hypothesis committee_in_nodes: forall s:slot, forall n:node, 
    incl (local_committees n s) nodes.

Lemma com_in_nodes: forall s:slot, forall n_v: node, 
    forall n_com:node,
    set_mem node_eq_dec n_com (local_committees n_v s) = true -> set_mem node_eq_dec n_com nodes = true.
    intros.
    apply set_mem_iff_list_in in H.
    rewrite set_mem_iff_list_in.
    apply committee_in_nodes with (s:=s)(n:=n_v). auto.
Qed.

Definition is_committee_maj_honest (nodes: set node): Prop:=
    let honest_nodes:= filter is_honest_bool nodes in
    2*(length honest_nodes) > length nodes.



Definition in_committee_for_bool (n:node) (s:slot) (view: node): bool:=
    set_mem node_eq_dec n (local_committees view s).

Definition in_committee_for (n:node) (s:slot) (view: node): Prop:=
    set_mem node_eq_dec n (local_committees view s) = true.

Definition is_honest_node (n:node):Prop:=
    is_honest n /\ set_mem node_eq_dec n nodes = true.
Definition is_honest_node_bool (n:node):bool:=
    is_honest_bool n && set_mem node_eq_dec n nodes. 

Variable delta: nat. (* the communication delay *)
Variable interact_duration: nat. (* the time for proposal-voting-aggregation step *)
Definition round_duration: nat := 8*delta. (* the upper limit of time for a round to last. *)
Definition slot_duration:nat := interact_duration + (n_committee+1) * round_duration.
(* the upper limit of time from entering slot to confirming a bk *)

Record ppT: Type := mkPPp {
    pp_slot: slot;
    pp_ppser: node;
    pp_value: nat;
    pp_prevhash: nat;     
}.


Record AggT: Type := mkAggP {
    ap_pp: ppT;
    ap_weight: nat;
}.

Record AckT: Type := mkAck {
    ack_ap: AggT;
    ack_voter: node; 
    ack_round: nat;
}.

Record AckpT: Type := mkAckp {
    ackp_ap: AggT;
    ackp_acks: set AckT;
    ackp_round: nat; 
}.

Record LPT: Type:=
    mkLp {
        lp_ap: AggT;
        lp_ppser: node; 
        lp_round: nat; 
        lp_ackp: option AckpT; (*previous cert*)
    }.

Record BlaT: Type := mkBlame {
    bl_slot: slot;
    bl_round: nat;
    bl_blamer: node;
}.

Record QBT: Type := mkQB {
    qb_slot: slot;
    qb_round: nat;
    qb_blames: set BlaT;  
}. 

Record QCT: Type := mkQC {
    qc_slot: slot;
    qc_round: nat;
    qc_lp1: LPT;
    qc_lp2: LPT;
}.

Inductive QuiT: Type :=
    | qt_conflict (qc: QCT)
    | qt_blame (qb: QBT).

Record CeT: Type := mkCert {
    ct_lp: LPT;
    ct_voter: node; 
    ct_ackp: AckpT; 
}.


Record FBkT:Type := mkFb {
    bk_lp: LPT;
    bk_proof: set CeT; 
}.



Inductive MsgCT: Type :=
    | apMsg (ap: AggT) (* send local winner to every com node. *)
    | lpMsg (lp:LPT) (* leader sends lp to every com node | com node forwards it to others *)
    | ackMsg (ack: AckT) (lp:LPT) (* com node acks to every com node *)
    | blameMsg (bl: BlaT) (* com node broadcasts blame to every com node *)
    | certMsg (cert:CeT) (* com node broadcasts cert to every com node (along with ackp) *)
    | ackpMsg (ackp: AckpT) (* com node send locked ackp to new leader *)
    | quitMsg (qt: QuiT) (* com node broadcasts/forwards to every com node *)
    | fbMsg (fb:FBkT). (* confirm msg: f+1 cert *) (* node broadcasts/forwards to every other node *)


Inductive TmoT: Type :=
    | tmo_int  (* wait for sometime, to forward the localWinner *)
    | tmo_lp (r:nat) (* if timeout, send blame *)
    | tmo_ack (r:nat) (* actually commit-timer *)
    | tmo_wait (r:nat) (* wait for 2 delta before sending highest witness *)
    | tmo_sta (r:nat) (* 4*delta waiting at the beginning of every round *)
    | tmo_act (* enter slot after confirming previous slot. *). (*all slots are currents slot. For act from s to s+1, the slot is s. *)


Inductive TriT: Type :=
    | tri_tmo (tmo_t: TmoT) (s:slot) (e_t:nat)
    | tri_msg (msg: MsgCT) (sender:node) (rcver:node) (send_time: nat). (* msg send time + rcv time*) (* use hypothesis to constrain rcv_time *)

Variable aggbk2hash: AggT->nat. 

Definition fb2hash (bk: FBkT): nat:=
    aggbk2hash bk.(bk_lp).(lp_ap).
Definition fb_prevhash (bk: FBkT): nat:=
    bk.(bk_lp).(lp_ap).(ap_pp).(pp_prevhash).
Definition fb2aggbk (bk: FBkT): AggT:=
    bk.(bk_lp).(lp_ap).

Variable agg_prevbk: AggT->FBkT. 
Definition full_prevbk (bk: FBkT): FBkT:=
    agg_prevbk bk.(bk_lp).(lp_ap).


(* prev_bk modeling the effect of hash chaining *)
Hypothesis aggprev_hash: 
    forall ap: AggT, 
    fb2hash (agg_prevbk ap) = ap.(ap_pp).(pp_prevhash).
    

Definition pp_beq (pp1 pp2: ppT):bool:=
    (pp1.(pp_slot) =? pp2.(pp_slot)) && (pp1.(pp_ppser) =? pp2.(pp_ppser)) && (pp1.(pp_value) =? pp2.(pp_value)) && (pp1.(pp_prevhash) =? pp2.(pp_prevhash)).

Definition ap_beq (ap1 ap2: AggT): bool:=
    (pp_beq ap1.(ap_pp) ap2.(ap_pp)) && (ap1.(ap_weight) =? ap2.(ap_weight)).

Definition ack_beq (ack1 ack2:AckT):bool:=
    ap_beq ack1.(ack_ap) ack2.(ack_ap) && (ack1.(ack_voter) =? ack2.(ack_voter)) && (ack1.(ack_round) =? ack2.(ack_round)).

Definition ackp_beq (ackp1 ackp2:AckpT):bool :=
    ap_beq ackp1.(ackp_ap) ackp2.(ackp_ap) && (ackp1.(ackp_round) =? ackp2.(ackp_round)) && list_beq AckT ack_beq ackp1.(ackp_acks) ackp2.(ackp_acks).


Definition lp_beq (lp1 lp2: LPT): bool:=
    ap_beq lp1.(lp_ap) lp2.(lp_ap) && (lp1.(lp_ppser) =? lp2.(lp_ppser)) && (lp1.(lp_round)=?lp2.(lp_round)) && 
    match lp1.(lp_ackp), lp2.(lp_ackp) with 
    | None, None => true
    | None, Some ackp2 => false
    | Some ackp1, None => false
    | Some ackp1, Some ackp2 => ackp_beq ackp1 ackp2
    end.

Definition bl_beq (bl1 bl2: BlaT): bool:=
    (bl1.(bl_slot) =? bl2.(bl_slot)) && (bl1.(bl_round) =? bl2.(bl_round)) && (bl1.(bl_blamer) =? bl2.(bl_blamer)).

Definition qb_beq (qb1 qb2: QBT): bool:=
    (qb1.(qb_slot) =? qb2.(qb_slot)) && (qb1.(qb_round) =? qb2.(qb_round)) && list_beq BlaT bl_beq qb1.(qb_blames) qb2.(qb_blames).

Definition qc_beq (qc1 qc2: QCT): bool:=
    (qc1.(qc_slot) =? qc2.(qc_slot)) && (qc1.(qc_round) =? qc2.(qc_round)) && (lp_beq qc1.(qc_lp1) qc2.(qc_lp1)) && (lp_beq qc1.(qc_lp2) qc2.(qc_lp2)).

Definition qt_beq (qt1 qt2: QuiT): bool:=
    match qt1, qt2 with 
    | qt_conflict qc1, qt_conflict qc2 => qc_beq qc1 qc2
    | qt_blame qb1, qt_blame qb2 => qb_beq qb1 qb2
    | _, _ => false
    end.


Definition ce_beq (ce1 ce2: CeT): bool:=
    (lp_beq ce1.(ct_lp) ce2.(ct_lp)) && (ce1.(ct_voter) =? ce2.(ct_voter)) && (ackp_beq ce1.(ct_ackp) ce2.(ct_ackp)).


Definition bk_equal (b1 b2: FBkT): Prop:=
    fb2aggbk b1 = fb2aggbk b2. 

Hypothesis lp_eq_dec: forall lp1 lp2: LPT, {lp1 = lp2} + {lp1 <> lp2}.

Hypothesis ack_eq_dec: forall ack1 ack2: AckT, {ack1 = ack2} + {ack1 <> ack2}.

Hypothesis bl_eq_dec: forall bl1 bl2: BlaT, {bl1 = bl2} + {bl1 <> bl2}.

Hypothesis ce_eq_dec: forall ce1 ce2: CeT, {ce1 = ce2} + {ce1 <> ce2}.


Definition fb_beq (fb1 fb2: FBkT): bool:=
    (lp_beq fb1.(bk_lp) fb2.(bk_lp)) && (list_beq CeT ce_beq fb1.(bk_proof) fb2.(bk_proof)).


Variable local_winner_s0: node->AggT. 
Variable honest_winner_s0: AggT.
Variable local_winner: node->slot->AggT->AggT. (* reflect that the block of slot s depends on previous chain.  *)
Variable honest_winner: slot->AggT->AggT.

Hypothesis local_winner_s0_is_fixed:
    forall n:node, forall prev_ap:AggT,
    local_winner n 0 prev_ap = local_winner_s0 n.
Hypothesis honest_winner_s0_is_fixed:
    forall prev_ap:AggT,
    honest_winner 0 prev_ap = honest_winner_s0.


Record State: Type:= mkState {
    st_node: node;
    st_slot: slot;

    st_int_done: bool; (* false -> true *)
    st_round: nat; 
    st_has_quit_round: bool; (* yes if during the waiting time *)
    
    
    st_confirmed_bk: option FBkT; 
    st_confirm_time: option nat;

    st_enter_slot_time: option nat; 

    st_local_winner: AggT;
    st_highest_winner: AggT; (* ap of largest weight received from all com nodes *)

    st_first_rcvd_lp: option LPT;
    st_first_rcv_lp_time: option nat; 
    st_acked_lp: option LPT;
    st_snd_rcvd_lp: option LPT;

    st_certified_bk: option LPT;
    st_certify_time: option nat;

    st_blames: set BlaT; (* blame of current slot and round *)

    st_acks: set AckT; (* only receive ack for first_rcvd_lp *)
    st_current_ackp: option AckpT; (* really lock at entering new round *)
    st_hlocked_prev_ackp: option AckpT; (* locked ackproof of the previous round *)
    st_forl_prev_ackp: option AckpT; (* only works for the leader. receive the highest prev_ackp in order to publish a lp along with the latest ackp. *)
    (* special: updates acorss round; after leaving the previous round. | initialized as None at leaving round. | send to leaders: if current_ackp exists, then current_ackp; otherwise previous locked highest.  *)

    st_leave_round_time: option nat;
    st_start_round_time: option nat;

    st_certs_nodes: LPT->set node; (* maintain the set of nodes. *)
    st_certs: LPT->set CeT; (* all certs corresponding to the lp *)
}.

Record Event: Type:= mkEvent {
    ev_time: nat; 
    ev_node: node; 
    ev_tri: TriT; 
}.

Definition empty_certs (lp:LPT): set CeT:=
    []. 

Definition empty_certs_nodes (lp:LPT): set node:=
    [].


(* already checked round | only check cert *)
Definition lp_is_valid (lp: LPT) (st: State): bool:=
    match st.(st_hlocked_prev_ackp), lp.(lp_ackp) with 
    | None, None => st.(st_local_winner).(ap_weight) <=? lp.(lp_ap).(ap_weight)
    | Some ackp, None => false
    | None, Some ackp' => true
    | Some ackp, Some ackp' => ackp.(ackp_round)<=? ackp'.(ackp_round)
    end.

Definition st_set_int_done (cs:State) (e_t:nat): State:=
    mkState cs.(st_node) cs.(st_slot) 
    true cs.(st_round) cs.(st_has_quit_round) 
    cs.(st_confirmed_bk) cs.(st_confirm_time) 
    cs.(st_enter_slot_time) 
    cs.(st_local_winner) cs.(st_highest_winner) 
    cs.(st_first_rcvd_lp) cs.(st_first_rcv_lp_time) cs.(st_acked_lp) cs.(st_snd_rcvd_lp) 
    cs.(st_certified_bk) cs.(st_certify_time) 
    cs.(st_blames)
    cs.(st_acks) cs.(st_current_ackp) cs.(st_hlocked_prev_ackp) cs.(st_forl_prev_ackp)
    cs.(st_leave_round_time) (Some e_t) 
    cs.(st_certs_nodes) cs.(st_certs).

Definition st_set_certify (cs:State) (e_t: nat) (lp: LPT) (ackp: AckpT): State:=
    mkState cs.(st_node) cs.(st_slot) 
    cs.(st_int_done) cs.(st_round) cs.(st_has_quit_round) 
    cs.(st_confirmed_bk) cs.(st_confirm_time) 
    cs.(st_enter_slot_time) 
    cs.(st_local_winner) cs.(st_highest_winner)
    cs.(st_first_rcvd_lp) cs.(st_first_rcv_lp_time) cs.(st_acked_lp) cs.(st_snd_rcvd_lp) 
    (Some lp) (Some e_t) 
    cs.(st_blames)
    cs.(st_acks) cs.(st_current_ackp) cs.(st_hlocked_prev_ackp)  cs.(st_forl_prev_ackp)
    cs.(st_leave_round_time) cs.(st_start_round_time)
    cs.(st_certs_nodes) cs.(st_certs).

Definition st_set_new_round (cs:State) (e_t:nat) (r:nat):State :=
    mkState cs.(st_node) cs.(st_slot) 
    cs.(st_int_done) r false 
    cs.(st_confirmed_bk) cs.(st_confirm_time) 
    cs.(st_enter_slot_time) 
    cs.(st_local_winner) cs.(st_highest_winner)
    None None None None 
    None None 
    [] 
    [] None cs.(st_current_ackp) cs.(st_forl_prev_ackp)
    None (Some e_t) 
    cs.(st_certs_nodes) cs.(st_certs).

Definition st_set_new_slot (cs:State) (l_winner:AggT): State:=
    mkState cs.(st_node) (S cs.(st_slot)) 
    false 0 false
    None None 
    None
    (l_winner) (l_winner)
    None None None None 
    None None
    [] 
    [] None None None
    None None 
    empty_certs_nodes empty_certs.

Definition st_set_highest_winner (cs:State) (ap:AggT):State :=
    mkState cs.(st_node) cs.(st_slot) 
    cs.(st_int_done) cs.(st_round) cs.(st_has_quit_round) 
    cs.(st_confirmed_bk) cs.(st_confirm_time) 
    cs.(st_enter_slot_time) 
    cs.(st_local_winner) (ap)
    cs.(st_first_rcvd_lp) cs.(st_first_rcv_lp_time) cs.(st_acked_lp) cs.(st_snd_rcvd_lp)
    cs.(st_certified_bk) cs.(st_certify_time) 
    cs.(st_blames)
    cs.(st_acks) cs.(st_current_ackp) cs.(st_hlocked_prev_ackp)  cs.(st_forl_prev_ackp)
    cs.(st_leave_round_time) cs.(st_start_round_time) 
    cs.(st_certs_nodes) cs.(st_certs).

Definition st_set_first_rcvd_lp (cs:State) (lp:LPT) (e_t:nat): State:=
    mkState cs.(st_node) cs.(st_slot) 
    cs.(st_int_done) cs.(st_round) cs.(st_has_quit_round) 
    cs.(st_confirmed_bk) cs.(st_confirm_time) 
    cs.(st_enter_slot_time) 
    cs.(st_local_winner) cs.(st_highest_winner) 
    (Some lp) (Some e_t) cs.(st_acked_lp) cs.(st_snd_rcvd_lp) 
    cs.(st_certified_bk) cs.(st_certify_time) 
    cs.(st_blames) 
    cs.(st_acks) cs.(st_current_ackp) cs.(st_hlocked_prev_ackp)  cs.(st_forl_prev_ackp)
    cs.(st_leave_round_time) cs.(st_start_round_time) 
    cs.(st_certs_nodes) cs.(st_certs).

Definition st_set_first_acked_lp (cs:State) (lp:LPT) (e_t:nat): State:=
    mkState cs.(st_node) cs.(st_slot) 
    cs.(st_int_done) cs.(st_round) cs.(st_has_quit_round)
    cs.(st_confirmed_bk) cs.(st_confirm_time) 
    cs.(st_enter_slot_time) 
    cs.(st_local_winner) cs.(st_highest_winner) 
    (Some lp) (Some e_t) (Some lp) cs.(st_snd_rcvd_lp)
    cs.(st_certified_bk) cs.(st_certify_time) 
    cs.(st_blames)
    cs.(st_acks) cs.(st_current_ackp) cs.(st_hlocked_prev_ackp)  cs.(st_forl_prev_ackp)
    cs.(st_leave_round_time) cs.(st_start_round_time) 
    cs.(st_certs_nodes) cs.(st_certs).

Definition st_set_qc (cs:State) (lp:LPT) (rcv_time: nat): State:= 
    mkState cs.(st_node) cs.(st_slot)
    cs.(st_int_done) cs.(st_round) true
    cs.(st_confirmed_bk) cs.(st_confirm_time) 
    cs.(st_enter_slot_time) 
    cs.(st_local_winner) cs.(st_highest_winner
    ) 
    cs.(st_first_rcvd_lp) cs.(st_first_rcv_lp_time) cs.(st_acked_lp) (Some lp) 
    cs.(st_certified_bk) cs.(st_certify_time)
    cs.(st_blames)
    cs.(st_acks) cs.(st_current_ackp) cs.(st_hlocked_prev_ackp)  None
    (Some rcv_time) cs.(st_start_round_time) 
    cs.(st_certs_nodes) cs.(st_certs).

Definition st_set_record_ack (cs:State) (ack: AckT) (rcv_time: nat): State:=
    mkState cs.(st_node) cs.(st_slot)
    cs.(st_int_done) cs.(st_round) cs.(st_has_quit_round)
    cs.(st_confirmed_bk) cs.(st_confirm_time) 
    cs.(st_enter_slot_time) 
    cs.(st_local_winner) cs.(st_highest_winner) 
    cs.(st_first_rcvd_lp) cs.(st_first_rcv_lp_time) cs.(st_acked_lp) cs.(st_snd_rcvd_lp) 
    cs.(st_certified_bk) cs.(st_certify_time)
    cs.(st_blames)
    ( (* since outer control makes sure that ap and round is the same, then only voter is different. *)
        set_add ack_eq_dec ack cs.(st_acks)) cs.(st_current_ackp) cs.(st_hlocked_prev_ackp) cs.(st_forl_prev_ackp)
    cs.(st_leave_round_time) cs.(st_start_round_time) 
    cs.(st_certs_nodes) cs.(st_certs).

Definition st_set_ackp (cs:State) (ackp:AckpT): State:=
    mkState cs.(st_node) cs.(st_slot)
    cs.(st_int_done) cs.(st_round) cs.(st_has_quit_round)
    cs.(st_confirmed_bk) cs.(st_confirm_time) 
    cs.(st_enter_slot_time) 
    cs.(st_local_winner) cs.(st_highest_winner) 
    cs.(st_first_rcvd_lp) cs.(st_first_rcv_lp_time) cs.(st_acked_lp) cs.(st_snd_rcvd_lp) 
    cs.(st_certified_bk) cs.(st_certify_time)
    cs.(st_blames)
    cs.(st_acks) (Some ackp) cs.(st_hlocked_prev_ackp) cs.(st_forl_prev_ackp)
    cs.(st_leave_round_time) cs.(st_start_round_time) 
    cs.(st_certs_nodes) cs.(st_certs).

Definition st_set_record_bla (cs:State) (bla:BlaT) (rcv_time:nat):State :=
    mkState cs.(st_node) cs.(st_slot)
    cs.(st_int_done) cs.(st_round) cs.(st_has_quit_round)
    cs.(st_confirmed_bk) cs.(st_confirm_time) 
    cs.(st_enter_slot_time) 
    cs.(st_local_winner) cs.(st_highest_winner) 
    cs.(st_first_rcvd_lp) cs.(st_first_rcv_lp_time) cs.(st_acked_lp) cs.(st_snd_rcvd_lp) 
    cs.(st_certified_bk) cs.(st_certify_time)
    (set_add bl_eq_dec bla cs.(st_blames))
    cs.(st_acks) cs.(st_current_ackp) cs.(st_hlocked_prev_ackp) cs.(st_forl_prev_ackp)
    cs.(st_leave_round_time) cs.(st_start_round_time) 
    cs.(st_certs_nodes) cs.(st_certs).

Definition st_set_qb (cs:State) (rcv_time:nat):State:=
    mkState cs.(st_node) cs.(st_slot)
    cs.(st_int_done) cs.(st_round) true
    cs.(st_confirmed_bk) cs.(st_confirm_time)
    cs.(st_enter_slot_time)
    cs.(st_local_winner) cs.(st_highest_winner)
    cs.(st_first_rcvd_lp) cs.(st_first_rcv_lp_time) cs.(st_acked_lp) cs.(st_snd_rcvd_lp)
    cs.(st_certified_bk) cs.(st_certify_time)
    cs.(st_blames)
    cs.(st_acks) cs.(st_current_ackp) cs.(st_hlocked_prev_ackp) None
    (Some rcv_time) cs.(st_start_round_time) 
    cs.(st_certs_nodes) cs.(st_certs).
    
    
Definition st_set_record_cert (cs:State) (cert: CeT) (rcv_time:nat):State :=
    if (set_mem node_eq_dec cert.(ct_voter) (cs.(st_certs_nodes) cert.(ct_lp))) then cs
    else
    mkState cs.(st_node) cs.(st_slot)
    cs.(st_int_done) cs.(st_round) cs.(st_has_quit_round)
    cs.(st_confirmed_bk) cs.(st_confirm_time)
    cs.(st_enter_slot_time)
    cs.(st_local_winner) cs.(st_highest_winner)
    cs.(st_first_rcvd_lp) cs.(st_first_rcv_lp_time) cs.(st_acked_lp) cs.(st_snd_rcvd_lp)
    cs.(st_certified_bk) cs.(st_certify_time)
    cs.(st_blames)
    cs.(st_acks) cs.(st_current_ackp) cs.(st_hlocked_prev_ackp) cs.(st_forl_prev_ackp)
    cs.(st_leave_round_time) cs.(st_start_round_time)
    (fun lp:LPT=> if (lp_beq lp cert.(ct_lp)) then set_add node_eq_dec cert.(ct_voter) (cs.(st_certs_nodes) lp) else cs.(st_certs_nodes) lp)
    (fun lp:LPT => if (lp_beq lp cert.(ct_lp)) then set_add ce_eq_dec cert (cs.(st_certs) lp) else cs.(st_certs) lp).


Definition st_set_confirm_bk (cs:State) (bk: FBkT) (e_t:nat): State:=
    mkState cs.(st_node) cs.(st_slot)
    cs.(st_int_done) cs.(st_round) true
    (Some bk) (Some e_t)
    cs.(st_enter_slot_time)
    cs.(st_local_winner) cs.(st_highest_winner)
    cs.(st_first_rcvd_lp) cs.(st_first_rcv_lp_time) cs.(st_acked_lp) cs.(st_snd_rcvd_lp)
    cs.(st_certified_bk) cs.(st_certify_time)
    cs.(st_blames)
    cs.(st_acks) cs.(st_current_ackp) cs.(st_hlocked_prev_ackp) None
    (Some e_t) cs.(st_start_round_time) 
    cs.(st_certs_nodes) cs.(st_certs).


Definition st_set_forl_ackp (cs:State) (ackp:AckpT):State:=
    mkState cs.(st_node) cs.(st_slot)
    cs.(st_int_done) cs.(st_round) cs.(st_has_quit_round)
    cs.(st_confirmed_bk) cs.(st_confirm_time)
    cs.(st_enter_slot_time)
    cs.(st_local_winner) cs.(st_highest_winner)
    cs.(st_first_rcvd_lp) cs.(st_first_rcv_lp_time) cs.(st_acked_lp) cs.(st_snd_rcvd_lp)
    cs.(st_certified_bk) cs.(st_certify_time)
    cs.(st_blames)
    cs.(st_acks) cs.(st_current_ackp) cs.(st_hlocked_prev_ackp) (Some ackp)
    cs.(st_leave_round_time) cs.(st_start_round_time) 
    cs.(st_certs_nodes) cs.(st_certs).

(* note that if confirmed, not move slot. Leave round, set act timeout. *)

Definition st_tr_tmo_1_int (cs:State) (e_t:nat): State:=
    if (cs.(st_int_done)) then cs
    else st_set_int_done cs e_t. (* trigger event: sending local winner to all com node. *)

(* lp-timer: 
    1. if has confirmed -> ignore
    2. if int not done -> should not happen | don't use the branch
    3. if round not match -> ignore 
    4. if has_quit_round -> ignore 
    5. if has rcved -> ignore 
    6. trigger blame -> not changing state. 
*)
Definition st_tr_tmo_2_lp (cs:State) (e_t:nat) (r:nat): State:=
    cs. (* not changing state. *)

(* ack timer - if timeout not quit: cert
    trigger-> forward cert. 
    set certified_bk certify_time
*)
Definition st_tr_tmo_3_ack (cs:State) (e_t:nat) (r:nat): State:=
    if (cs.(st_has_quit_round)) then cs (* includes confirm. *)
    else 
        match cs.(st_acked_lp) with
        | None => cs (* should not happen *)
        | Some lp => 
            match cs.(st_current_ackp) with
            | None => cs (* not enough acks *)
            | Some ackp =>
            st_set_certify cs e_t lp ackp 
            end
        end.    

(* quit_round. after wait, enter new round*)
Definition st_tr_tmo_4_wait (cs:State) (e_t:nat) (r:nat): State:=
    match cs.(st_confirmed_bk) with
    | Some bk => cs (* should not happen *) (* includes confirmed slot*)
    | None =>
        if (negb cs.(st_has_quit_round)) then cs 
        else st_set_new_round cs e_t r
    end.

Definition st_tr_tmo_5_sta (cs:State) (e_t:nat) (r:nat): State:=
    cs. (* trigger leader broadcasting lps. No state changes *)

Definition st_tr_tmo_6_act (cs:State) (e_t:nat): State:=
    match cs.(st_confirmed_bk) with
    | Some bk => st_set_new_slot cs (fb2aggbk bk)
    | None => cs (* should not happen: the old round must be confirmed. *)
    end. (* result of confirming a slot. Cannot confirm another slot in between. *)


(* receiving ap from com_node. might update their own *)
(* only happen in/before round 0 *)
Definition st_tr_msg_1_ap (cs:State) (sender:node) (rcv_time:nat) (ap: AggT): State:=
    match cs.(st_confirmed_bk) with 
    | Some bk => cs (* don't need any more actions*)
    | None => 
        (* ap slot match *)
        if (ap.(ap_pp).(pp_slot)=?cs.(st_slot)) then 
        if (in_committee_for_bool sender cs.(st_slot) cs.(st_node)) then
        if (cs.(st_highest_winner).(ap_weight) <? ap.(ap_weight)) then 
                st_set_highest_winner cs ap
        else cs (* don't need to update highest winner *)
        else cs (* slot not match *)
        else cs
    end.

(* receiving lp: most complicated: 
    1. if slot confirmed already -> ignore 
    2. if int not done -> ignore 
    3. if round not match -> ignore 
    4. if has_quit_round -> ignore 
    5. if not leader -> ignore 
    6. not received before -> set first_rcvd_lp & forward. If valid, broadcast and starts timer. 
    7. received before -> quit_round, broadcast qc. 
*)

Definition st_tr_msg_2_lp (cs:State) (sender:node) (rcv_time:nat) (lp: LPT): State:=
    match cs.(st_confirmed_bk) with
    | Some bk => cs
    | None =>
        if (negb cs.(st_int_done)) then cs
        else 
            if (lp.(lp_round) =? cs.(st_round)) then
            if (in_committee_for_bool sender cs.(st_slot) cs.(st_node)) then
            if (cs.(st_has_quit_round)) then cs
            else
                if (local_committee_leaders cs.(st_node) cs.(st_slot) cs.(st_round) =? lp.(lp_ppser)) then
                match cs.(st_first_rcvd_lp) with
                | None => 
                    if lp_is_valid lp cs then 
                        st_set_first_acked_lp cs lp rcv_time
                    else st_set_first_rcvd_lp cs lp rcv_time 
                | Some lp' => 
                    if (lp_beq lp lp') then 
                        cs 
                    else 
                        st_set_qc cs lp rcv_time (* will broadcast qc *)
                end
                else cs
            else cs
        else cs
    end.


(* when receive ack in the round, if same block, add to *)

(* different from 2_lp: mainly to deal with ack. Problem: when the lp is the first time rcved => if valid, set first_rcvd, set acked, add to acks. | invalid. set first_rcvd. (2) if the lp is different from already received => not record. . (3) in wait time: ignore then. Will only consider receiving complete ackp in wait time.  *)
Definition st_tr_msg_3_ack (cs:State) (sender:node) (rcv_time:nat) (ack: AckT) (lp:LPT): State:=
    match cs.(st_confirmed_bk) with
    | Some bk => cs
    | None =>
        if (negb cs.(st_int_done)) then cs
        else 
            if (lp.(lp_round) =? cs.(st_round)) then
            if (in_committee_for_bool sender cs.(st_slot) cs.(st_node)) then
            if (cs.(st_has_quit_round)) then cs
            else
                if (local_committee_leaders cs.(st_node) cs.(st_slot) cs.(st_round) =? lp.(lp_ppser)) then
                if (ap_beq lp.(lp_ap) ack.(ack_ap))
                then 
                match cs.(st_first_rcvd_lp) with
                | None => 
                    if lp_is_valid lp cs then 
                        let tmp_st:= 
                        st_set_record_ack (st_set_first_acked_lp cs lp rcv_time) ack rcv_time
                        in if(n_committee <=? length tmp_st.(st_acks))
                        then st_set_ackp tmp_st (mkAckp ack.(ack_ap) tmp_st.(st_acks) ack.(ack_round)) else tmp_st
                    else st_set_first_rcvd_lp cs lp rcv_time 
                | Some lp' => 
                    if (lp_beq lp lp') then 
                        let tmp_st:=
                        st_set_record_ack cs ack rcv_time
                        in if(n_committee <=? length tmp_st.(st_acks))
                        then st_set_ackp tmp_st (mkAckp ack.(ack_ap) tmp_st.(st_acks) ack.(ack_round)) else tmp_st
                    else 
                        st_set_qc cs lp rcv_time (* will broadcast qc *)
                end
                else cs
            else cs
            else cs
        else cs
    end.

Definition st_tr_msg_4_blame (cs:State) (sender:node) (rcv_time:nat) (bl: BlaT): State:=
    match cs.(st_confirmed_bk) with
    | Some bk => cs
    | None => 
        if (negb cs.(st_int_done)) then cs
        else 
        if (bl.(bl_slot) =? cs.(st_slot)) then
            if (bl.(bl_round) =? cs.(st_round)) then
            if (cs.(st_has_quit_round)) then cs
            else 
            if (in_committee_for_bool sender cs.(st_slot) cs.(st_node)) then (* the sender must be in committee *)
                let tmp_st:=
                    st_set_record_bla cs bl rcv_time
                in if (n_committee <=? length tmp_st.(st_blames)) then st_set_qb tmp_st rcv_time
                else cs 
            else cs
        else cs
        else cs
    end.

(* rcv cert: parse the ackp from it. *)
Definition st_tr_msg_5_cert (cs:State) (sender:node) (rcv_time:nat) (cert: CeT): State:=
    match cs.(st_confirmed_bk) with
    | Some bk => cs
    | None =>
        if (negb cs.(st_int_done)) then cs
        else 
        if (cert.(ct_lp).(lp_round) =? cs.(st_round)) then
        let tmp_st:=
        st_set_record_cert cs cert rcv_time
        in (* if enough cert -> confirm | broadcast conf-bk *)
        if (n_committee <=? length (tmp_st.(st_certs) cert.(ct_lp))) then
            let bk:= mkFb cert.(ct_lp) (tmp_st.(st_certs) cert.(ct_lp)) in st_set_confirm_bk tmp_st bk rcv_time
        else cs
        else cs
    end.

Definition st_tr_msg_6_ackp (cs:State) (sender:node) (rcv_time:nat) (ackp: AckpT): State:=
    match cs.(st_confirmed_bk) with
    | Some bk => cs
    | None =>
        match cs.(st_forl_prev_ackp) with
        | None => st_set_forl_ackp cs ackp
        | Some ackp' => 
            if (ackp'.(ackp_round)<? ackp.(ackp_round)) then cs
            else st_set_forl_ackp cs ackp
        end
    end.

(* will set quit if not quited *)
Definition st_tr_msg_7_quit (cs:State) (sender:node) (rcv_time:nat) (qt: QuiT): State:=
    match cs.(st_confirmed_bk) with
    | Some bk => cs
    | None =>
        if (cs.(st_has_quit_round)) then cs
        else 
            match qt with 
            | qt_conflict qc =>
                if (qc.(qc_slot) =? cs.(st_slot)) then
                if (qc.(qc_round) =? cs.(st_round)) then
                st_set_qc cs qc.(qc_lp1) rcv_time
                else cs
                else cs
            | qt_blame qb =>
                if (qb.(qb_slot) =? cs.(st_slot)) then
                if (qb.(qb_round) =? cs.(st_round)) then
                st_set_qb cs rcv_time
                else cs
                else cs
            end
    end.


(* will forward it to others *)
Definition st_tr_msg_8_fb (cs:State) (sender:node) (rcv_time:nat) (fb: FBkT): State:=
    match cs.(st_confirmed_bk) with
    | Some bk => cs
    | None =>
        st_set_confirm_bk cs fb rcv_time
    end.

Definition st_tr_tmo (cs:State) (tmo_t:TmoT) (s:nat) (e_t:nat): State:=
    if (s=?cs.(st_slot)) then
    match tmo_t with 
    | tmo_int => st_tr_tmo_1_int cs e_t 
    | tmo_lp r => st_tr_tmo_2_lp cs e_t r
    | tmo_ack r => st_tr_tmo_3_ack cs e_t r
    | tmo_wait r => st_tr_tmo_4_wait cs e_t r
    | tmo_sta r => st_tr_tmo_5_sta cs e_t r
    | tmo_act => st_tr_tmo_6_act cs e_t 
    end
    else cs.

Definition st_tr_msg (cs:State) (msg: MsgCT) (sender:node) (send_time: nat) (ev_time: nat): State:=
    match msg with
    | apMsg ap => st_tr_msg_1_ap cs sender ev_time ap
    | lpMsg lp => st_tr_msg_2_lp cs sender ev_time lp
    | ackMsg ack lp => st_tr_msg_3_ack cs sender ev_time ack lp
    | blameMsg bl => st_tr_msg_4_blame cs sender ev_time bl
    | certMsg cert => st_tr_msg_5_cert cs sender ev_time cert
    | ackpMsg ackp => st_tr_msg_6_ackp cs sender ev_time ackp
    | quitMsg qt => st_tr_msg_7_quit cs sender ev_time qt
    | fbMsg fb => st_tr_msg_8_fb cs sender ev_time fb
    end. 

(* state-transition: branches by event  *)
Definition st_tr (cs: State) (ev: Event): State :=
    if (ev.(ev_node) =? cs.(st_node)) then 
        match ev.(ev_tri) with
        | tri_tmo tmo_t s e_t => 
            st_tr_tmo cs tmo_t s e_t
        | tri_msg msg sender rcver send_time => 
            st_tr_msg cs msg sender send_time ev.(ev_time)
        end
    else cs
    .

Definition st_tr_op (cs: State) (ev: option Event): State :=
    match ev with
    | None => cs
    | Some ev' => st_tr cs ev'
    end.


Definition initial_states (n: node) :State:=
    mkState n 0 false 0 false None None None (local_winner_s0 n) (honest_winner_s0) None None None None None None [] [] None None None None None 
    empty_certs_nodes empty_certs.

Variable node_id_to_event: node->nat->option Event. 

Fixpoint state_before_node_id (n:node) (i:nat):State:=
    match i with 
    | 0 => initial_states n
    | S i' => let prev_state:= state_before_node_id n i' in
        match node_id_to_event n i' with
        | None => prev_state
        | Some ev => st_tr prev_state ev
        end
    end.

Definition state_after_node_id (n:node) (i:nat): State:=
    state_before_node_id n (S i).


Lemma state_before_node_id_tr:
    forall n:node, forall i:nat, 
        state_before_node_id n (S i) = 
        st_tr_op (state_before_node_id n i) (node_id_to_event n i).
    intros.
Admitted. (* trivial *)

Lemma state_after_node_id_tr:
    forall n:node, forall i:nat, 
        state_after_node_id n (S i) = 
        st_tr_op (state_after_node_id n i) (node_id_to_event n (S i)).
Admitted. (* trivial *)

Variable confirmed_bk: node->slot->option FBkT. 

Variable enter_slot_seqid: node->slot->nat. 
Definition enter_slot_time (n:node) (s:slot):=
    match node_id_to_event n (enter_slot_seqid n s) with 
    | None => 0
    | Some ev => ev.(ev_time)
    end. 
Variable confirm_slot_seqid: node->slot->nat. 
Definition confirm_slot_time (n:node) (s:slot):=
    match node_id_to_event n (confirm_slot_seqid n s) with
    | None => 0
    | Some ev => ev.(ev_time)
    end. 


Variable certified_bk: node->slot->nat->option LPT. 

Variable first_rcvd_lp: node->slot->nat->option LPT.

Variable last_round: node->slot->option nat. (* maybe the slot never stops. *)
Variable start_round_time: node->slot->nat->nat. 
Variable leave_round_time: node->slot->nat->nat. 
(* for rounds > last_round, the above time is meaningless *)
Variable quit_round_proof: node->slot->nat->option QuiT. 
Variable has_confirmed_in_slot_round: node->slot->nat->Prop. 

(* everyone really quited_round if and only if the following two cases happen:
    1. receive f+1 cert. Then everyone will quit soon. 
    2. receive f+1 blame or conflict. Then everyone will also quit soon. 
*)


Definition broadcast_msgs_to (msg: MsgCT) (sender:node) (recipients: set node) (send_time: nat): list TriT:=
    let evs:= map (fun rcver => (tri_msg msg sender rcver send_time)) recipients in
    evs.


Definition triggers_tmo (prev_st:State) (next_st:State) (tmo_t:TmoT) (s:nat) (e_t:nat): list TriT:=
    match tmo_t with
    | tmo_int => 
        let rcvers:= local_committees prev_st.(st_node) s in
        broadcast_msgs_to (apMsg prev_st.(st_local_winner)) prev_st.(st_node) rcvers e_t ++ 
        [tri_tmo (tmo_lp 0) s (e_t + 4*delta)]
    | tmo_lp r => 
        if (prev_st.(st_round) =? r) then 
        if (prev_st.(st_has_quit_round)) then []
        else 
            match prev_st.(st_first_rcvd_lp) with
            | None =>
                let rcvers:= local_committees prev_st.(st_node) s in
                broadcast_msgs_to (blameMsg (mkBlame prev_st.(st_slot) prev_st.(st_round) prev_st.(st_node))) prev_st.(st_node) rcvers e_t
            | Some already_rcved_lp => []
            end
        else []
    | tmo_ack r => 
        if (prev_st.(st_round) =? r) then 
        if (prev_st.(st_has_quit_round)) then []
        else 
            match prev_st.(st_acked_lp) with
            | None => []
            | Some acked_lp => 
                let rcvers:= local_committees prev_st.(st_node) s in
                if ((length prev_st.(st_acks) <? n_committee) && (n_committee <=? length prev_st.(st_acks))) then
                    broadcast_msgs_to (certMsg (mkCert acked_lp prev_st.(st_node) (mkAckp acked_lp.(lp_ap) next_st.(st_acks) prev_st.(st_round)))) prev_st.(st_node) rcvers e_t
                else []
            end
        else []
    | tmo_wait r => 
        (* prev_round -> next_round | send locked ackp to new leader *)
        if (prev_st.(st_round) =? r) then
        if (next_st.(st_round) =? S r) then
        let rcver:= local_committee_leaders prev_st.(st_node) s (S r) in
        match next_st.(st_hlocked_prev_ackp) with
        | None => []
        | Some ackp => 
            [tri_msg (ackpMsg ackp) prev_st.(st_node) rcver e_t]
        end ++ [tri_tmo (tmo_lp (S r)) s (e_t + 4*delta)]
        else []
        else []
    | tmo_sta r => 
        if (prev_st.(st_round) =? r) then 
        if (prev_st.(st_has_quit_round)) then []
        else 
            let rcvers:= local_committees prev_st.(st_node) s in
            match prev_st.(st_forl_prev_ackp) with
            | None => broadcast_msgs_to (lpMsg (mkLp prev_st.(st_highest_winner) prev_st.(st_node) prev_st.(st_round) None)) prev_st.(st_node) rcvers e_t
            | Some ackp => broadcast_msgs_to (lpMsg (mkLp ackp.(ackp_ap) prev_st.(st_node) prev_st.(st_round) (Some ackp))) prev_st.(st_node) rcvers e_t
            end
        else []
    | tmo_act => 
        if (local_committee_leader_order prev_st.(st_node) s prev_st.(st_node) =? 0) then
        [tri_tmo (tmo_sta 0) s (e_t + interact_duration+2*delta)]
        else [] 
        ++ [tri_tmo (tmo_int) s (e_t + interact_duration+delta)]
    end.

Definition triggers_msg (prev_st:State) (next_st:State) (msg: MsgCT) (sender:node) (rcv_time: nat): list TriT:=
    match msg with
    | apMsg ap => []
    | lpMsg lp => (* if first_lp => broadcast | might ack *)
        if (in_committee_for_bool prev_st.(st_node) prev_st.(st_slot) prev_st.(st_node)) then
        if (prev_st.(st_has_quit_round)) then []
        else
        let rcvers:= local_committees prev_st.(st_node) prev_st.(st_slot) in
            match prev_st.(st_first_rcvd_lp) with
            | Some first_lp => 
                if (next_st.(st_has_quit_round)) then (* conflicting lp => broadcast qc & start wait timer *)
                let qc_msg:= quitMsg (qt_conflict (mkQC prev_st.(st_slot) prev_st.(st_round) first_lp lp)) in
                (broadcast_msgs_to qc_msg sender rcvers rcv_time) ++ [tri_tmo (tmo_wait prev_st.(st_round)) prev_st.(st_slot) (rcv_time + 2*delta)]
                else [] (* no need to do anything *)
            | None =>
                match next_st.(st_first_rcvd_lp), next_st.(st_acked_lp) with 
                | None, None => []
                | None, Some ack_lp => [] (* should not happen *)
                | Some rcv_lp, None => (* only rcv, not ack *)
                    broadcast_msgs_to (lpMsg lp) sender rcvers rcv_time
                | Some rcv_lp, Some ack_lp => (* broadcast lp and ack, start ack timer *)
                    let ack:= mkAck lp.(lp_ap) prev_st.(st_node) prev_st.(st_round) in
                    broadcast_msgs_to (lpMsg lp) sender rcvers rcv_time ++ broadcast_msgs_to (ackMsg ack lp) sender rcvers rcv_time ++ [tri_tmo (tmo_ack prev_st.(st_round)) prev_st.(st_slot) (rcv_time + 2*delta)]
                end
            end
        else []
       
    | ackMsg ack lp => (* only trigger: if first_lp => forward lp | might ack . If not first_lp | might qc *)
        if (prev_st.(st_has_quit_round)) then []
        else
        let com_nodes:= local_committees prev_st.(st_node) prev_st.(st_slot) in
        match prev_st.(st_first_rcvd_lp), prev_st.(st_acked_lp), next_st.(st_first_rcvd_lp), next_st.(st_acked_lp) with 
        | None, None, Some lp1, Some lp2 => (* forward lp and ack and ack timer *)
            broadcast_msgs_to (lpMsg lp) sender com_nodes rcv_time ++ broadcast_msgs_to (ackMsg (mkAck lp.(lp_ap) prev_st.(st_node) prev_st.(st_round)) lp) sender com_nodes rcv_time ++ [tri_tmo (tmo_ack prev_st.(st_round)) prev_st.(st_slot) (rcv_time + 2*delta)]
        | None, None, Some lp1, None => (* forward lp but not ack*)
            broadcast_msgs_to (lpMsg lp) sender com_nodes rcv_time
        | Some lp1, _, _, _ => (* check if lp same *)
            if (lp_beq lp1 lp) then []
            else broadcast_msgs_to (quitMsg (qt_conflict (mkQC prev_st.(st_slot) prev_st.(st_round) lp1 lp))) sender com_nodes rcv_time ++ [tri_tmo (tmo_wait prev_st.(st_round)) prev_st.(st_slot) (rcv_time + 2*delta)]
        | _,_,_,_ => []
        end

    (* if enough blame, broadcast qb*)
    | blameMsg bl => 
        if (prev_st.(st_has_quit_round)) then []
        else if (length prev_st.(st_blames) <? n_committee)
        then if (n_committee <=? length next_st.(st_blames))
        then let rcvers:= local_committees prev_st.(st_node) prev_st.(st_slot) in
            broadcast_msgs_to (quitMsg (qt_blame (mkQB prev_st.(st_slot) prev_st.(st_round) prev_st.(st_blames)))) sender rcvers rcv_time
        else []
        else []
    (* if not forwarded, forward it. | enough -> confirm *)
    | certMsg cert => 
        if (in_nodeset_bool cert.(ct_voter) (prev_st.(st_certs_nodes) cert.(ct_lp))) then []
        else 
        let rcvers:= local_committees prev_st.(st_node) prev_st.(st_slot) in
        broadcast_msgs_to (certMsg cert) sender rcvers rcv_time ++
        if (length (prev_st.(st_certs) cert.(ct_lp)) <? n_committee)
        then if (n_committee <=? length (next_st.(st_certs) cert.(ct_lp)))
        then broadcast_msgs_to (fbMsg (mkFb cert.(ct_lp) (next_st.(st_certs) cert.(ct_lp)))) sender rcvers rcv_time
        else []
        else []
    | _ => []
    end.

Definition triggers_by_node_id (n:node) (i:nat):list TriT:=
    match node_id_to_event n i with
    | None => []
    | Some ev => 
        let prev_st:= state_before_node_id n i in
        let next_st:= state_after_node_id n i in
        match ev.(ev_tri) with (* *)
        | tri_tmo tmo_t s e_t => 
            triggers_tmo prev_st next_st tmo_t s e_t
        | tri_msg msg sender rcver send_time => 
            (* if rcver =? n then ｜ guaranteed by node_id_to_event. all events must be for the node. state is also for the node. *)
            triggers_msg prev_st next_st msg sender ev.(ev_time) 
            
        end
    end.

(* define properties of events *)

(* now the triggers are defined. link them with events *)

Hypothesis tmo_triggered_at_expire_time:
    forall n:node, forall i:nat, forall ev: Event, forall tmo_t:TmoT, forall s:nat, forall e_t:nat,
        node_id_to_event n i = Some ev ->
        ev.(ev_tri) = (tri_tmo tmo_t s e_t) ->
        ev.(ev_time) = e_t. 

(* msgcontent, sender, receiver, send_time -> determines receive time *)
Variable msg_rcved_time: MsgCT->node->node->nat->nat. 

Hypothesis msg_rcv_time_diff:
    forall sender rcver:node, forall msg:MsgCT, forall send_time:nat,
    is_honest_node sender -> is_honest_node rcver ->
    msg_rcved_time msg sender rcver send_time >= send_time /\ msg_rcved_time msg sender rcver send_time <= send_time + delta.

Hypothesis msg_triggered_at_receive_time:
    forall n:node, forall i:nat, forall ev:Event, forall msg:MsgCT, forall sender rcver:node, forall send_time:nat,
        is_honest_node n ->
        node_id_to_event n i = Some ev ->
        ev.(ev_tri) = (tri_msg msg sender rcver send_time) ->
        ev.(ev_time) = msg_rcved_time msg sender rcver send_time.

Hypothesis event_node_is_n:
    forall n:node, forall i:nat, forall ev:Event,
        node_id_to_event n i = Some ev -> ev.(ev_node) = n.

Hypothesis event_time_monotone: 
    forall n:node, forall i1 i2:nat, forall ev1 ev2:Event,
        
        i1 < i2 -> node_id_to_event n i1 = Some ev1 -> node_id_to_event n i2 = Some ev2 -> ev1.(ev_time) <= ev2.(ev_time).

Hypothesis event_continuous:
    forall n:node, forall i1 i2 i3:nat, forall ev1 ev3:Event,
        
        i1 < i2 -> i2 < i3 -> node_id_to_event n i1 = Some ev1 -> node_id_to_event n i3 = Some ev3 -> 
        exists ev2, node_id_to_event n i2 = Some ev2.


(* When receiving lp exactly at the same time as lp-timer runs out, we count it as receiving lp on time. 
    The below hypothesis helps this:
    - receiving lp before lp-timer runs out -> not blame
    - receiving enough ack exactly before ack-timer runs out -> still cert
    - receiving ack exactly before wait-timer runs out -> records the ack. 
    - receiving ackp exactly before status-timer runs out -> updates the ackp in proposing lp. 
*)
Hypothesis event_priority_msg_before_tmo:
    forall n:node, forall i1 i2:nat, forall ev1 ev2:Event,
        forall msg:MsgCT, forall sender rcver:node, forall send_time:nat, forall tmo_t:TmoT, forall s:nat, forall e_t:nat, 
        node_id_to_event n i1 = Some ev1 -> node_id_to_event n i2 = Some ev2 -> 
        ev1.(ev_time) = ev2.(ev_time) ->
        ev1.(ev_tri) = tri_msg msg sender rcver send_time -> ev2.(ev_tri) = tri_tmo tmo_t s e_t -> i1 < i2. 

Definition event_0 (n:node): Event :=
    mkEvent 0 n (tri_tmo tmo_act 0 0). 

(* note that tmo type if for the same node | but msg type can be for every node *)
Hypothesis all_tmo_triggers_happen:
    forall n:node, forall i:nat, forall ev:Event, 
        is_honest_node n ->
        node_id_to_event n i = Some ev -> 
        forall tr:TriT, forall tmo_t:TmoT, forall s:slot, forall et:nat, 
        In tr (triggers_by_node_id n i) ->
        tr = tri_tmo tmo_t s et ->
        exists e':Event, exists i':nat, i'>i /\ 
        node_id_to_event n i' = Some e' /\ e'.(ev_node) = n /\ e'.(ev_time) = et.

Hypothesis all_msg_triggers_happen:
    forall n:node, forall i:nat, forall ev:Event, 
        is_honest_node n ->
        node_id_to_event n i = Some ev -> 
        forall tr:TriT, forall msg:MsgCT, forall sender rcver:node, forall send_time:nat,
        In tr (triggers_by_node_id n i) ->
        tr = tri_msg msg sender rcver send_time ->
        is_honest_node rcver ->
        exists e':Event, exists i':nat,  
        node_id_to_event rcver i' = Some e' /\ e'.(ev_node) = rcver /\ e'.(ev_time) = msg_rcved_time msg sender rcver send_time.

Hypothesis all_events_have_triggers:
    forall n:node, forall i:nat, forall ev:Event, 
        is_honest_node n ->
        node_id_to_event n i = Some ev -> 
        i>=1 -> (* the first event is defined by default *)
        match ev.(ev_tri) with
        | tri_tmo tmo_t s e_t => 
            exists i':nat, i'< i /\
            In (tri_tmo tmo_t s e_t) (triggers_by_node_id n i')
        | tri_msg msg sender rcver send_time =>
            is_honest_node sender -> 
            exists i':nat, In (tri_msg msg sender rcver send_time) (triggers_by_node_id sender i')
        end.

Lemma nonemptyset_exists: 
    forall setx: set node,
    length setx > 0 -> exists n:node, set_mem node_eq_dec n setx = true.
    intros.
    destruct_with_eqn setx.
    inversion H.
    exists n. simpl. unfold node_eq_dec.
    destruct (Nat.eq_dec n n); auto. 
Qed.



Lemma setfilter_cond:
    forall setx: set node, forall f: node->bool,
    let subset:= filter f setx in
    forall n:node, set_mem node_eq_dec n subset = true -> set_mem node_eq_dec n setx = true /\ f n = true.
    intros.
    apply set_mem_iff_list_in in H.
    rewrite set_mem_iff_list_in.
    apply filter_In.
    auto.
Qed.


Lemma in_com_in_leader_order:
    forall n_v n_l:node, forall s:slot, 
    is_honest_node n_v ->
    in_committee_for n_l s n_v ->
    local_committee_leader_order n_v s n_l < n_committee.
Admitted. 

Lemma in_leaders_in_leader_orders:
    forall n_v n_l:node, forall s:slot, forall r:nat, 
    is_honest_node n_v->
    r < n_committee ->
    local_committee_leaders n_v s r = n_l ->
    local_committee_leader_order n_v s n_l = r.
Admitted. 

Lemma in_order_in_leaders:
    forall n_v n_l:node, forall s:slot, 
    is_honest_node n_v->
    local_committee_leader_order n_v s n_l < n_committee ->
    local_committee_leaders n_v s (local_committee_leader_order n_v s n_l) = n_l /\ (forall k:nat, local_committee_leaders n_v s ((local_committee_leader_order n_v s n_l) + k*n_committee) = n_l).
Admitted. 


Lemma not_in_leaders_order:
    forall n_v n_l:node, forall s:slot,
    is_honest_node n_v -> 
        (forall r:nat, local_committee_leaders n_v s r <> n_l) ->
        local_committee_leader_order n_v s n_l = n_committee.
Admitted. 

Lemma order_n_not_in_leaders:
    forall n_v n_l:node, forall s:slot, 
    is_honest_node n_v ->
        local_committee_leader_order n_v s n_l = n_committee ->
        (forall r:nat, local_committee_leaders n_v s r <> n_l).
Admitted. 



Hypothesis honest_majority: forall s:slot, forall n:node, 
    is_honest_node n -> is_committee_maj_honest (local_committees n s).

Hypothesis exists_honest_node:
    exists h_n:node, is_honest_node h_n.




Hypothesis confirmed_bk_none_keeps_none: forall s:slot, forall n:node, 
    confirmed_bk n s = None -> confirmed_bk n (S s) = None.

Lemma confirmed_bk_some_implies_some: forall s:slot, forall n:node, forall bk: FBkT,
    confirmed_bk n (S s) = Some bk -> exists b, confirmed_bk n s = Some b.
    intros.
    destruct_with_eqn (confirmed_bk n s).
    exists f. auto.
    apply confirmed_bk_none_keeps_none in Heqo. congruence.
Qed.


Hypothesis local_winner_at_least_high_as_honest:
    forall s:slot, forall prev_ap:AggT, 
    forall n:node, 
    (local_winner n s prev_ap).(ap_weight) >= (honest_winner s prev_ap).(ap_weight).

Lemma local_winner_s0_at_least_high_as_honest:
    forall n:node, 
    (local_winner_s0 n).(ap_weight) >= (honest_winner_s0).(ap_weight).
    intros.
    assert (local_winner n 0 honest_winner_s0 = local_winner_s0 n).
    apply local_winner_s0_is_fixed.
    assert (honest_winner 0 honest_winner_s0 = honest_winner_s0).
    apply honest_winner_s0_is_fixed.
    rewrite <- H0. rewrite <- H. 
    apply local_winner_at_least_high_as_honest with (s:=0)(prev_ap:=honest_winner_s0)(n:=n).
Qed.

Definition confirm_same_bk_pred (s:slot): Prop:=
    exists aggPrp: AggT, forall n:node,
    is_honest_node n ->
    exists bk: FBkT,
    confirmed_bk n s = Some bk /\ fb2aggbk bk = aggPrp. 


Lemma confirm_implies_honest_certify:
    forall s:slot, forall n:node, forall fb:FBkT,
    is_honest_node n ->
    confirmed_bk n s = Some fb ->
    exists com:node, is_honest_node com /\ in_committee_for com s n /\ let lp:= fb.(bk_lp) in
    certified_bk com s lp.(lp_round) = Some lp.
Admitted. 


Hypothesis com_leaders_determined_by_prevbks:
    forall s:slot, forall n1 n2:node, forall bk1 bk2: FBkT,
    is_honest_node n1 -> is_honest_node n2 ->
    confirmed_bk n1 s = Some bk1 -> 
    confirmed_bk n2 s = Some bk2 ->
    bk_equal bk1 bk2 ->

    local_committee_leaders n1 (S s) = local_committee_leaders n2 (S s). 

Hypothesis com_leaders_same_s0:
    forall n1 n2:node, 
    is_honest_node n1 -> is_honest_node n2 ->
    local_committee_leaders n1 0 = local_committee_leaders n2 0.


Lemma com_leaders_implies_leader_order:
    forall n1 n2:node, forall s:slot, 
    is_honest_node n1 -> is_honest_node n2 ->
    local_committee_leaders n1 s = local_committee_leaders n2 s ->
    local_committee_leader_order n1 s = local_committee_leader_order n2 s.

Admitted.

Lemma leader_order_implies_com_leaders:
    forall n1 n2:node, forall s:slot, 
    is_honest_node n1 -> is_honest_node n2 ->
    local_committee_leader_order n1 s = local_committee_leader_order n2 s ->
    local_committee_leaders n1 s = local_committee_leaders n2 s.
Admitted. 

Lemma com_leaders_implies_committee:
    forall n1 n2:node, forall s:slot, 
    is_honest_node n1 -> is_honest_node n2 ->
    local_committee_leaders n1 s = local_committee_leaders n2 s ->
    local_committees n1 s = local_committees n2 s.
Admitted. 

Lemma committee_determined_by_prevbks:
    forall s:slot, forall n1 n2:node, forall bk1 bk2: FBkT,
    is_honest_node n1 -> is_honest_node n2 ->
    confirmed_bk n1 s = Some bk1 -> 
    confirmed_bk n2 s = Some bk2 ->
    bk_equal bk1 bk2 ->

    local_committees n1 (S s) = local_committees n2 (S s).
    intros.
    apply com_leaders_implies_committee. auto. auto.
    apply com_leaders_determined_by_prevbks with (s:=s)(n1:=n1)(n2:=n2)(bk1:=bk1)(bk2:=bk2). auto. auto. auto. auto. auto. 
Qed. 

Lemma committee_same_s0:
    forall n1 n2:node, 
    is_honest_node n1 -> is_honest_node n2 ->
    local_committees n1 0 = local_committees n2 0.
    intros.

    apply com_leaders_implies_committee. auto. auto. 
    apply com_leaders_same_s0. auto. auto.
Qed. 


Variable lp_rcved_at_n1_acked_by_n2: LPT->node->node->slot->nat->Prop. (* the lp received by node for slot and round, before leaving the round *)
Variable lp_in_ackproof_node_slot_round: LPT->node->slot->nat->Prop. (* form at the end of the round. *)
(* ackproof formed in these ways: [1] receiving ack in the round before leaving_round+delta delay, [2] certify msg carries the ackproof, [3] leader receive locked ackproof during round change, [4] parsing the ackproof in lp. *)

(* variable determined by state (node, id). defined standalone to facilitate reference*)
Variable locked_ackproof: 
    node->slot->nat->option AckpT.

Variable highest_locked_ackproof:
    node->slot->nat->option AckpT. (* if in round r, a locked ackp is formed, but in round r+1, no locked ackp is formed. Then the latest locked ackproof of round r+1 is the ackproof of round r. *)

(* note that the first_rcv_lp is just valid in format: [1] come from the leader, [2] claimed round matches. It may not be acknowledged. Therefore, acknowledge bk is different from first_rcv_lp. Acknowledged bk if exists is the first_rcv_lp && it is valid in terms of carrying witness.  *)

Variable acked_lp: node->slot->nat->option LPT.

Variable first_rcv_lp_time: node->slot->nat->nat. 

Variable snd_rcvd_lp: node->slot->nat->option LPT. (* only valid if rcved before first_rcv_time and 2delta later. *)

Variable certify_time: node->slot->nat->nat.  

Lemma certify_time_2d_rcv_lp:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n:node, forall r:nat, forall lp:LPT,
    is_honest_node n ->
    in_committee_for n s n ->
    r = lp.(lp_round) -> certified_bk n s r = Some lp -> (* really certified *)
    certify_time n s r = first_rcv_lp_time n s r + 2*delta.
    (* as the result of ack timer *)
Admitted. 

Lemma first_rcv_lp_is_forwarded:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n:node, forall r:nat,
    forall lp:LPT, 
    is_honest_node n ->
    in_committee_for n s n ->
    first_rcvd_lp n s r = Some lp ->
    forall other:node,
    is_honest_node other ->
    in_committee_for other s other ->
    (* make sure other has not left round *)
    first_rcv_lp_time n s r + delta <= leave_round_time other s r ->
     exists lp1, first_rcvd_lp other s r = Some lp1 /\ (lp1=lp -> first_rcv_lp_time other s r <= first_rcv_lp_time n s r + delta). 
Admitted. 



Lemma ack_rcved_only_if_acked:
    forall acker rcver:node, forall s:slot, forall r:nat,
    forall lp:LPT, 
    is_honest_node acker ->
    in_committee_for acker s acker ->
    is_honest_node rcver ->
    lp_rcved_at_n1_acked_by_n2 lp rcver acker s r ->
    acked_lp acker s r = Some lp.
Admitted. 

Lemma ack_only_if_first_rcv_lp:
    forall n:node, forall s:slot, forall r:nat,
    forall lp:LPT, 
    is_honest_node n ->
    in_committee_for n s n ->
    acked_lp n s r = Some lp ->
    first_rcvd_lp n s r = Some lp.
Admitted. 

Lemma acked_lp_has_cert_from_h_ack:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall new_acker: node, forall r:nat, forall lp:LPT, forall ackp:AckpT, 
    is_honest_node new_acker ->
    in_committee_for new_acker s new_acker ->
    acked_lp new_acker s (S r) = Some lp -> 
    highest_locked_ackproof new_acker s r = Some ackp ->
    exists ackp1:AckpT, exists old_acker: node, exists old_lp: LPT,  lp.(lp_ackp) = Some ackp1 /\ ackp1.(ackp_round) >= ackp.(ackp_round) /\ ackp1.(ackp_ap) = lp.(lp_ap) /\
    is_honest_node old_acker /\ in_committee_for old_acker s old_acker /\ acked_lp old_acker s old_lp.(lp_round) = Some old_lp /\ old_lp.(lp_ap) = ackp1.(ackp_ap) /\ old_lp.(lp_round) = ackp1.(ackp_round). 

Admitted. 
    

Lemma allH_ack_forms_proof:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall r:nat, forall lp:LPT, forall rcver: node, 
    (forall acker:node, is_honest_node acker-> in_committee_for acker s acker -> lp_rcved_at_n1_acked_by_n2 lp rcver acker s r) -> lp_in_ackproof_node_slot_round lp rcver s r.
Admitted. 

Lemma not_ack_if_not_highest_ackproof:
    forall n:node, forall s:slot, forall r:nat, forall lp:LPT, forall ackp:AckpT,
    is_honest_node n ->
    in_committee_for n s n ->
    acked_lp n s (S r) = Some lp ->
    highest_locked_ackproof n s r = Some ackp ->
    exists ackp1:AckpT, lp.(lp_ackp) = Some ackp1 /\ ackp1.(ackp_round) >= ackp.(ackp_round). 
Admitted. 

Lemma locked_ackproof_in_ackproof:
    forall n:node, forall s:slot, forall r:nat, forall ackp:AckpT,
    is_honest_node n ->
    in_committee_for n s n ->
    locked_ackproof n s r = Some ackp -> 
    exists lp:LPT, 
    lp_in_ackproof_node_slot_round lp n s r /\ lp.(lp_ap) = ackp.(ackp_ap) /\ lp.(lp_round) = ackp.(ackp_round).
Admitted. 
Lemma highest_cert_exists_if_exists:
    forall n:node, forall s:slot, forall r:nat, 
    forall ackp:AckpT, 
    is_honest_node n ->
    in_committee_for n s n ->
    highest_locked_ackproof n s r = Some ackp ->
    exists ackp1:AckpT, highest_locked_ackproof n s (S r) = Some ackp1 /\ ackp1.(ackp_round)>= ackp.(ackp_round).
Admitted. 

Lemma highest_ackp_implies_hack:
    forall s:slot,
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n:node, forall r:nat,
    forall ackp:AckpT,
    is_honest_node n ->
    in_committee_for n s n ->
    highest_locked_ackproof n s r = Some ackp -> 
    exists n1:node, exists lp:LPT, 
    is_honest_node n1 /\ in_committee_for n1 s n1 /\
    ackp.(ackp_ap) = lp.(lp_ap) /\ ackp.(ackp_round) = lp.(lp_round) /\ acked_lp n1 s lp.(lp_round) = Some lp.

Admitted. 

Lemma ackproof_and_no_h_ack_implies_locked:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall r:nat, forall lp:LPT, forall n: node, 
    lp_in_ackproof_node_slot_round lp n s r ->
    (forall acker:node, forall lp1:LPT, is_honest_node acker -> in_committee_for acker s acker -> acked_lp acker s r = Some lp1 -> lp1 = lp) ->
    exists ackp:AckpT, locked_ackproof n s r = Some ackp /\ ackp.(ackp_ap) = lp.(lp_ap) /\ ackp.(ackp_round) = r.
Admitted.  

Lemma locked_current_is_highest_ackproof:
    forall n:node, forall s:slot, forall r:nat, forall ackp:AckpT,
    is_honest_node n ->
    in_committee_for n s n ->
    locked_ackproof n s r = Some ackp -> 
    highest_locked_ackproof n s r = Some ackp.
Admitted. 

Lemma highest_ackproof_round_bound:
    forall n:node, forall s:slot, forall r:nat, 
    forall ackp:AckpT,
    is_honest_node n ->
    in_committee_for n s n ->
    highest_locked_ackproof n s r = Some ackp -> ackp.(ackp_round) <= r.

Admitted. 

Lemma acked_cert_round_bound:
    forall n:node, forall s:slot, forall r:nat,
    forall lp:LPT, forall ackp:AckpT,
    is_honest_node n ->
    in_committee_for n s n ->
    acked_lp n s (S r) = Some lp -> 
    lp.(lp_ackp) = Some ackp -> ackp.(ackp_round) <= r.
Admitted. 

Lemma lp_with_cert_carries_the_same_ap:
    forall n:node, forall s:slot, forall r:nat, 
    forall lp:LPT, forall ackp:AckpT,
    is_honest_node n ->
    in_committee_for n s n ->
    acked_lp n s (S r) = Some lp ->
    lp.(lp_ackp) = Some ackp -> 
    lp.(lp_ap) = ackp.(ackp_ap).
Admitted.  

Lemma cert_bk_is_first_rcvd:
    forall n:node, forall s:slot, forall r:nat, 
    forall lp:LPT,
    is_honest_node n ->
    in_committee_for n s n ->
    certified_bk n s r = Some lp ->
    first_rcvd_lp n s r = Some lp.
Admitted. 

Lemma first_lp_diff_time:
    forall s:slot,
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n n1:node, forall r:nat, forall lp lp1:LPT,
    is_honest_node n ->
    in_committee_for n s n ->
    is_honest_node n1 ->
    in_committee_for n1 s n1 ->
    first_rcvd_lp n s r = Some lp ->
    first_rcvd_lp n1 s r = Some lp1 ->
    lp <> lp1 ->
    first_rcv_lp_time n s r <= 
    first_rcv_lp_time n1 s r + delta.
Admitted. 

Lemma snd_rcvd_lp_cond:
    forall s:slot,
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n n1:node, forall r:nat, forall lp lp1:LPT,
    is_honest_node n ->
    in_committee_for n s n ->
    is_honest_node n1 ->
    in_committee_for n1 s n1 ->
    first_rcvd_lp n s r = Some lp ->
    first_rcvd_lp n1 s r = Some lp1 ->
    lp <> lp1 ->
    first_rcv_lp_time n1 s r + delta <= leave_round_time n s r ->
    exists lp2, snd_rcvd_lp n s r = Some lp2.
Admitted. 

Lemma snd_rcvd_lp_implies_no_cert:
    forall n:node, forall s:slot, forall r:nat,
    forall lp1:LPT,
    is_honest_node n ->
    in_committee_for n s n ->
    snd_rcvd_lp n s r = Some lp1 ->
    certified_bk n s r = None.

Admitted. 

Lemma cert_before_leaving_round:
    forall n:node, forall s:slot, forall r:nat, forall lp:LPT,
    is_honest_node n ->
    in_committee_for n s n ->
    certified_bk n s r = Some lp ->
    certify_time n s r <= leave_round_time n s r.
Admitted.  

Lemma leave_round_d_delay:
    forall s:slot,
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n n1:node, forall r:nat, 
    is_honest_node n ->
    in_committee_for n s n ->
    is_honest_node n1 ->
    in_committee_for n1 s n1 ->
    leave_round_time n s r <= leave_round_time n1 s r + delta.
Admitted. 

Lemma cert_implies_ackproof:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall r:nat, forall lp:LPT, forall n:node,
    is_honest_node n ->
    in_committee_for n s n ->
    certified_bk n s r = Some lp ->
    lp.(lp_round) = r ->
    exists ackp:AckpT, (locked_ackproof n s r = Some ackp /\ ackp.(ackp_ap) = lp.(lp_ap) /\ ackp.(ackp_round) = r /\ 
    (
        forall n1:node, is_honest_node n1 -> in_committee_for n1 s n1 ->
        exists ackp1:AckpT, locked_ackproof n1 s r = Some ackp1 /\ ackp1.(ackp_ap) = lp.(lp_ap) /\ ackp1.(ackp_round) = r
    )
    ).

Admitted. 

Lemma enter_slot_time_diff:
    forall s:slot,
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n1 n2:node,
    is_honest_node n1 -> is_honest_node n2 ->
    enter_slot_time n1 s <= enter_slot_time n2 s + delta. 
Admitted. 

Lemma has_confirmed_remain_round:
    forall n:node, forall s:slot, forall r:nat,
    is_honest_node n ->
    in_committee_for n s n ->
    has_confirmed_in_slot_round n s r -> has_confirmed_in_slot_round n s (S r).
Admitted. 

Lemma com_confirm_time:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n:node, forall r:nat, 
    is_honest_node n ->
    in_committee_for n s n ->
    has_confirmed_in_slot_round n s r ->
    confirm_slot_time n s <= enter_slot_time n s + interact_duration + (r+1)*round_duration.

Admitted. 


Lemma one_confirmed_other_confirm_round:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n1 n2:node, forall r:nat, 
    is_honest_node n1 -> is_honest_node n2 ->
    in_committee_for n1 s n1 -> in_committee_for n2 s n2 ->
    has_confirmed_in_slot_round n1 s r ->
    has_confirmed_in_slot_round n2 s r \/ has_confirmed_in_slot_round n2 s (S r). 

Admitted. 

Lemma one_confirm_other_confirm_noncom:
    forall s:slot,
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n1 n2:node, 
    is_honest_node n1 -> is_honest_node n2 ->
    forall b1:FBkT, 
    confirmed_bk n1 s = Some b1 -> 
    exists b2: FBkT, confirmed_bk n2 s = Some b2 /\ bk_equal b1 b2 /\ confirm_slot_time n2 s <= confirm_slot_time n1 s + delta. 
Admitted. 

Lemma bk_implies_committee_same_s1:
    forall s:slot, 
    confirm_same_bk_pred s ->
    exists coms: set node, forall n:node, is_honest_node n ->
    local_committees n (S s) = coms. 

    intros.
    (* assume that there exist an honest node. use its coms.  *)
    destruct exists_honest_node as [n_h].
    remember (local_committees n_h (S s)) as coms.
    exists coms.
    intros.
    unfold confirm_same_bk_pred in H.
    destruct H as [aggPrp].

    pose proof H0 as H0'.
    apply H in H0'.
    destruct H0' as [bk1].
    destruct H2.

    pose proof H1 as H1'.
    apply H in H1'.
    destruct H1' as [bk2].
    destruct H4.

    assert (bk_equal bk2 bk1).
    unfold bk_equal. rewrite H3. rewrite H5. auto.
    
    rewrite Heqcoms.
    apply committee_determined_by_prevbks with (s:=s)(n1:=n)(n2:=n_h) (bk1:=bk2)(bk2:=bk1). auto. auto. auto. auto. auto. 
Qed.


Lemma bk_implies_committee_pair_equal:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n1 n2:node,
    is_honest_node n1 -> is_honest_node n2 ->
    local_committees n1 s = local_committees n2 s.

Admitted. 

Lemma bk_implies_committee_view_pair_equal:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall com n1 n2:node,
    is_honest_node n1 -> is_honest_node n2 ->
    in_committee_for com s n1 -> in_committee_for com s n2.
Admitted. 


(* same slot, same round implication. *)
Lemma honest_cert_implies_honest_ack:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall r:nat, forall lp:LPT,
    forall n:node, is_honest_node n ->
    in_committee_for n s n ->
    certified_bk n s r = Some lp ->
   acked_lp n s r = Some lp.

Admitted. 


Lemma exists_honest_com_node:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    exists n_hc:node,  in_committee_for n_hc s n_hc /\ is_honest_node n_hc /\ local_committee_leader_order n_hc s n_hc < n_committee.
    intros.

    destruct exists_honest_node as [n_h].
    pose proof H0 as G.
    apply honest_majority with (s:=s)(n:=n_h) in G .
    unfold is_committee_maj_honest in G.
    remember (local_committees n_h s) as coms.
    remember (filter is_honest_bool coms) as honest_coms.
    assert (length honest_coms >0).
    lia.
    assert (exists n:node, set_mem node_eq_dec n honest_coms = true).
    apply nonemptyset_exists. auto.
    destruct H2.
    exists x. 

    assert (in_committee_for x s n_h /\ is_honest_bool x = true).
    unfold in_committee_for.
    rewrite <- Heqcoms. 

    (* a node from honest_coms is both honest and in_com *)
    rewrite Heqhonest_coms in H2.
    unfold is_honest_node.
    apply setfilter_cond in H2.
    destruct H2. split. auto. auto. 
    
    
    destruct H3.
    split. auto.
    apply bk_implies_committee_view_pair_equal with (s:=s)(n1:=n_h)(n2:=x)(com:=x). auto. auto. unfold is_honest_node. split. auto. 
    
    apply com_in_nodes with (s:=s)(n_v:=n_h). rewrite <- Heqcoms. 

    apply setfilter_cond with (setx:= coms) (f:=is_honest_bool)(n:=x). rewrite <- Heqhonest_coms. auto. auto.

    assert (is_honest_node x).

    unfold is_honest_node. split. auto.
    assert (set_mem node_eq_dec x coms = true).
    rewrite Heqhonest_coms in H2.
    apply setfilter_cond with (setx:=coms)(f:=is_honest_bool)(n:=x). auto. 
    apply com_in_nodes with (s:=s)(n_v:=n_h). rewrite <- Heqcoms. auto. auto.

    split. auto.
    apply in_com_in_leader_order with (n_v:=x) (s:=s). auto. auto.
    apply bk_implies_committee_view_pair_equal with (s:=s)(n1:=n_h)(n2:=x)(com:=x). auto. auto. auto. auto.

Qed.


Lemma important_lemma: 
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n:node, forall lp: LPT,
    is_honest_node n ->
    in_committee_for n s n ->
    certified_bk n s lp.(lp_round) = Some lp ->
    (forall n1: node, is_honest_node n1 -> 
    in_committee_for n1 s n1 ->
    exists ackp: AckpT, locked_ackproof n1 s lp.(lp_round) = Some ackp /\ ackp.(ackp_ap) = lp.(lp_ap) /\ackp.(ackp_round) = lp.(lp_round)) /\ (* part 1: every other has ackproof *)
    (forall n2:node, is_honest_node n2->
    in_committee_for n2 s n2 ->
    forall lp1:LPT, first_rcvd_lp n2 s lp.(lp_round) = Some lp1-> lp1 = lp).

    (* PROOF *)

    intros.
    (* step 1: cert at t => rcv lp at t-2d => others rcv lp before t-d, before leaving slot. *)

    assert ((certify_time n s lp.(lp_round)) <= (leave_round_time n s lp.(lp_round))) as Hcert_leave.
    apply cert_before_leaving_round with (n:=n) (s:=s) (r:=lp.(lp_round)) (lp:=lp). auto. auto. auto. auto.
    remember (certify_time n s lp.(lp_round)) as t0.
    remember (leave_round_time n s lp.(lp_round)) as t_leave.
    
    remember (first_rcv_lp_time n s lp.(lp_round)) as t1.
    assert (t0 = (t1 + 2*delta)) as Htrcv_tcert.
    rewrite Heqt0. rewrite Heqt1.
    apply certify_time_2d_rcv_lp with (n:=n) (s:=s) (r:=lp.(lp_round)) (lp:=lp). auto. auto. auto. auto. auto.

    
    assert ((first_rcvd_lp n s lp.(lp_round)) = Some lp) as Hrcv_lp.
    apply cert_bk_is_first_rcvd with (n:=n) (s:=s) (r:=lp.(lp_round)) (lp:=lp). auto. auto. auto. 


    assert (forall other:node, is_honest_node other ->in_committee_for other s other -> first_rcvd_lp other s lp.(lp_round) = Some lp /\ first_rcv_lp_time other s lp.(lp_round) <= t0-delta).

    (* at t1, first_rcv_implies forwarding, and receiving *)
    intros.

    assert (leave_round_time n s lp.(lp_round) <= leave_round_time other s lp.(lp_round) + delta) as Hleave_leave.
    apply leave_round_d_delay with (n:=n) (n1:=other) (s:=s) (r:=lp.(lp_round)). auto. auto. auto. auto. auto. 

    assert (leave_round_time other s lp.(lp_round) >= t1+delta) as Hotherleave_t1.
    lia.

    pose proof Hrcv_lp as Hrcv_lp_temp.
    apply first_rcv_lp_is_forwarded with (n:=n) (s:=s) (r:=lp.(lp_round)) (lp:=lp) (other:=other) in Hrcv_lp_temp. all:auto.  2:{rewrite <- Heqt1. lia. }
    destruct Hrcv_lp_temp as [lp1 [Hlp1 Hrcv_rcv]].
    (* destruct: lp1=lp or lp!=lp *)
    destruct (lp_eq_dec lp lp1).
    rewrite <-e in Hlp1. 
    split. auto. rewrite <- e in Hrcv_rcv. 
    rewrite <- Heqt1 in Hrcv_rcv. replace (t0-delta) with (t1+delta). apply Hrcv_rcv.  auto. lia.

    (* lp!=lp1 *)
    (* receive lp1 by t0 => not certify *)
    assert (exists lp2, snd_rcvd_lp n s lp.(lp_round) = Some lp2) as Hlp2.
    apply snd_rcvd_lp_cond with (n:=n) (n1:=other) (s:=s) (r:=lp.(lp_round)) (lp:=lp) (lp1:=lp1). all:auto. 
    (* to show that t_leave after receiving the other lp*)
    assert (first_rcv_lp_time other s lp.(lp_round) <= first_rcv_lp_time n s lp.(lp_round) + delta) as H_leave_before_rcv_other.
    apply first_lp_diff_time with (n:=other) (n1:=n) (s:=s) (r:=lp.(lp_round)) (lp:=lp1) (lp1:=lp). all:auto. lia.
    destruct Hlp2 as [lp2 Hlp2].
    assert (certified_bk n s lp.(lp_round) = None).
    apply snd_rcvd_lp_implies_no_cert with (n:=n) (s:=s) (r:=lp.(lp_round)) (lp1:=lp2). all:auto. congruence.

    (* now every other node accepts this  *)
    (* should prove the second result first. It is used in the first result. *)
    assert (forall other:node, is_honest_node other -> in_committee_for other s other -> forall lp1:LPT, first_rcvd_lp other s lp.(lp_round) = Some lp1 -> lp1 = lp) as Hother_rcv_lp.
    intros.
    assert (first_rcvd_lp other s lp.(lp_round) = Some lp) as Hlp.
    apply H3 with (other:=other). all:auto. 
    rewrite Hlp in H6.
    inversion H6. auto. 

    split.
    2:auto.

    intros.

    apply cert_implies_ackproof with (s:=s) (r:=lp.(lp_round)) (lp:=lp) (n:=n) in H2.
    destruct H2 as [ackp [H2_1 [H2_2 [H2_3 H2_4]]]].
    apply H2_4 with (n1:=n1). all:auto.
Qed.


(* If every-h locks on a lp-ackp of round at least r, and show that no honest node every acks different ap in rounds [r, r+p]. Then no-honest node acks different ap in round r+p+1.  *)
Lemma important_lemma_across_rounds_helper1:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall lp: LPT, forall r_gap:nat,
    let base_round:= lp.(lp_round) in
    (
        forall n1:node, is_honest_node n1 -> in_committee_for n1 s n1 -> 
        (exists ackp, highest_locked_ackproof n1 s (base_round+r_gap) = Some ackp /\ ackp.(ackp_ap) = lp.(lp_ap) /\ ackp.(ackp_round) >= base_round)
    ) ->
    ( (*cannot provide other ackp*)
        forall rd:nat, rd >= base_round -> rd<= base_round + r_gap -> forall n2:node, is_honest_node n2 -> in_committee_for n2 s n2 -> 
        forall lp2:LPT, acked_lp n2 s rd = Some lp2 -> lp2.(lp_ap) = lp.(lp_ap)
    ) -> 
    (
        forall n3:node, is_honest_node n3 -> in_committee_for n3 s n3 -> 
        forall lp3:LPT, acked_lp n3 s (base_round + r_gap + 1) = Some lp3 -> lp3.(lp_ap) = lp.(lp_ap)
    ). (* easy to show that no alternative latest ackp can be formed, since in the new round, no honest acks a different ap *)
    
    (* start of proof.  *)
    intros.
    assert (exists ackp: AckpT, highest_locked_ackproof n3 s (base_round+r_gap) = Some ackp /\ ackp.(ackp_ap) = lp.(lp_ap)/\ ackp.(ackp_round)>=base_round).
    apply H0. auto. auto.
    destruct H5 as [ackp [Hackp1 [Hackp2 Hackp3]]].
    (* since the person acking in the new round has ackp, the acked lp must has cert-ackp at round at least as high. *)
    replace (base_round+r_gap+1) with (S (base_round+r_gap)) in H4 by lia.
    assert (exists ackp1:AckpT, lp3.(lp_ackp) = Some ackp1 /\ ackp1.(ackp_round) >= ackp.(ackp_round)).
    apply not_ack_if_not_highest_ackproof with (n:=n3) (s:=s) (r:=(base_round+r_gap)) (lp:=lp3) (ackp:=ackp). 
    auto. auto. auto. auto.

    destruct H5 as [ackp1 [Hlp1_1 Hlp1_2]].
    assert(exists ackp1:AckpT, exists old_acker: node, exists old_lp: LPT,  lp3.(lp_ackp) = Some ackp1 /\ ackp1.(ackp_round) >= ackp.(ackp_round) /\ ackp1.(ackp_ap) = lp3.(lp_ap) /\
    is_honest_node old_acker /\ in_committee_for old_acker s old_acker /\ acked_lp old_acker s old_lp.(lp_round) = Some old_lp /\ old_lp.(lp_ap) = ackp1.(ackp_ap) /\ old_lp.(lp_round) = ackp1.(ackp_round)).
    
    apply acked_lp_has_cert_from_h_ack with (new_acker:=n3) (s:=s) (r:=(base_round+r_gap)) (lp:=lp3) (ackp:=ackp). auto. auto. auto. auto. auto. 

    destruct H5 as [ackp2 [old_acker [old_lp [Hlp3cert [Hackp1round_1 [Hackp1_ap [Hold_h [Hold_c [Hold_ack_lp [H_old_lp_ap H_old_lp_round]]]]]]]]]].
    (* the lp1 is acked, with round >= ackp1s round *)
    assert (ackp2 = ackp1) as Hack''. rewrite Hlp1_1 in Hlp3cert. inversion Hlp3cert. auto.

    rewrite Hack'' in H_old_lp_ap. rewrite Hack'' in Hackp1round_1. rewrite Hack'' in H_old_lp_round. 
    rewrite Hack'' in Hackp1_ap. 

    (* now, we have the acked lp in the new round. *)
    (* we need to show that no other ap is acked. *)
    assert (old_lp.(lp_round) >= ackp.(ackp_round)) as H_old_round. lia.
    assert (old_lp.(lp_round) >= base_round) as H_old_round2. lia.

    assert (ackp1.(ackp_round)<=base_round+r_gap) as H_ackp1_round_bound.
    apply acked_cert_round_bound with (n:=n3) (s:=s) (r:=base_round+r_gap) (lp:=lp3) (ackp:=ackp1). auto. auto. auto. auto.
    assert (old_lp.(lp_round) <= base_round+r_gap) as H_old_round_upper. lia.

    assert (old_lp.(lp_ap) = lp.(lp_ap)) as H_old_ap.
    apply H1 with (rd:=old_lp.(lp_round))(n2:=old_acker)(lp2:=old_lp). auto. auto. auto. auto. auto.

    rewrite <- Hackp1_ap. 
    rewrite <- H_old_lp_ap. auto.

Qed.

Lemma important_lemma_across_rounds_helper2:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall lp: LPT, forall r_gap:nat,
    let base_round:= lp.(lp_round) in
    (
        forall n1:node, is_honest_node n1 -> in_committee_for n1 s n1 -> 
        (exists ackp, highest_locked_ackproof n1 s (base_round+r_gap) = Some ackp /\ ackp.(ackp_ap) = lp.(lp_ap) /\ ackp.(ackp_round) >= base_round)
    ) ->
    ( (*cannot provide other ackp*)
        forall rd:nat, rd >= base_round -> rd<= base_round + r_gap -> forall n2:node, is_honest_node n2 -> in_committee_for n2 s n2 -> 
        forall lp2:LPT, acked_lp n2 s rd = Some lp2 -> lp2.(lp_ap) = lp.(lp_ap)
    ) -> 
    (
        forall n3:node, is_honest_node n3 -> in_committee_for n3 s n3 -> 
        (
            exists ackp: AckpT, highest_locked_ackproof n3 s (base_round+r_gap+1) = Some ackp /\ ackp.(ackp_ap) = lp.(lp_ap) /\ ackp.(ackp_round) >= base_round
        )
    ).
    intros.
    assert (forall n4:node, is_honest_node n4 -> in_committee_for n4 s n4 -> 
        forall lp3:LPT, acked_lp n4 s (base_round + r_gap + 1) = Some lp3 -> lp3.(lp_ap) = lp.(lp_ap)).
    apply important_lemma_across_rounds_helper1 with (s:=s) (lp:=lp) (r_gap:=r_gap). auto. auto. auto. 
    
    assert (exists ackp:AckpT, highest_locked_ackproof n3 s (base_round +r_gap) = Some ackp /\ ackp_ap ackp = lp_ap lp /\ ackp_round ackp >= base_round) as Hold_ackp.

    apply H0. auto. auto.

    destruct Hold_ackp as [ackp [Hackp_locked [Hackp_ap Hackp_round]]].

    assert (exists ackp1:AckpT, highest_locked_ackproof n3 s (S (base_round+r_gap)) = Some ackp1 /\ ackp1.(ackp_round) >= ackp.(ackp_round)) as Hnew_ackp.
    apply highest_cert_exists_if_exists with (n:=n3) (s:=s) (r:=base_round+r_gap) (ackp:=ackp). all:auto.
    
    destruct Hnew_ackp as [ackp1 [Hnew_ackp_ap Hnew_ackp_round]].
    exists ackp1.

    split. replace (base_round+r_gap+1) with (S (base_round+r_gap)) by lia. auto. split. 2:lia. 

    (* now showing the new ackp has the same ap. Ackp-> hack*)
    
    assert (exists acker:node, exists other_lp:LPT, 
    is_honest_node acker /\ in_committee_for acker s acker /\
    ackp1.(ackp_ap) = other_lp.(lp_ap) /\ ackp1.(ackp_round) = other_lp.(lp_round) /\ acked_lp acker s other_lp.(lp_round) = Some other_lp) as H_other_ack.
    apply highest_ackp_implies_hack with (n:=n3) (s:=s) (r:= S(base_round+r_gap)) (ackp:=ackp1). all:auto. 

    destruct H_other_ack as [acker [other_lp [Hacker [Hacker_c [Hackp1_ap [Hackp1_round Hack_lp]]]]]].
    rewrite Hackp1_ap.
    rewrite <- Hackp1_round in Hack_lp. 

    assert (ackp1.(ackp_round) <= S (base_round + r_gap)) as Hackp1_round_u_bound.
    apply highest_ackproof_round_bound with (n:=n3) (s:=s) (r:=S (base_round+r_gap)) (ackp:=ackp1). auto. auto. auto.

    assert (ackp1.(ackp_round) >= base_round) as Hackp1_round_l_bound. lia.

    assert ({ackp1.(ackp_round)<= (base_round+r_gap)} + {ackp1.(ackp_round)>(base_round+r_gap)}).
    apply le_gt_dec with (n:=ackp1.(ackp_round)) (m:=base_round+r_gap).

    destruct H5.
    apply H1 with (rd:=ackp1.(ackp_round)) (n2:=acker) (lp2:=other_lp). auto. auto. auto. auto. auto.
    assert (ackp_round ackp1 = base_round + r_gap+ 1) by lia.
    apply H4 with (n4:=acker) (lp3:=other_lp). auto. auto. 
    replace (base_round+r_gap+1) with (S (base_round+r_gap)) by lia. rewrite H5 in Hack_lp. 
    replace (base_round+r_gap+1) with (S (base_round+r_gap)) in Hack_lp by lia. auto.

Qed.


Lemma important_lemma_across_rounds_helper_ultra:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n:node, forall lp: LPT,
    is_honest_node n ->
    in_committee_for n s n ->
    certified_bk n s lp.(lp_round) = Some lp ->

    forall r_gap:nat, 
    let base_round:= lp.(lp_round) in 
    (
        forall n1:node, is_honest_node n1 ->
        in_committee_for n1 s n1 ->
        exists ackp:AckpT, highest_locked_ackproof n1 s (base_round + r_gap) = Some ackp /\ ackp.(ackp_ap) = lp.(lp_ap) /\ ackp.(ackp_round) >= base_round
    ) /\
    (
        forall round1:nat, round1>=base_round ->
        round1 <= base_round + r_gap ->
        forall n2:node, is_honest_node n2 -> in_committee_for n2 s n2 ->
        forall lp1:LPT, acked_lp n2 s round1 = Some lp1 -> lp1.(lp_ap) = lp.(lp_ap)
    ).

    (* start of proof *)
    intros.
    induction r_gap.
    (* base case *)
    replace (base_round+0) with base_round by lia.
    split.
    intros.
    pose proof H as Htemp.
    apply important_lemma with (s:=s) (n:=n) (lp:=lp) in Htemp. all:auto.
    destruct Htemp as [Hackp_exist H2_ack_ap].
    assert (exists ackp:AckpT, locked_ackproof n1 s base_round = Some ackp /\ ackp.(ackp_ap) = lp.(lp_ap) /\ ackp.(ackp_round) = base_round) as Hackp_cons.
    apply Hackp_exist. auto. auto. 

    destruct Hackp_cons as [ackp [Hlock_ackp [Hackp_ap Hackp_round]]].
    exists ackp. split. 
    apply locked_current_is_highest_ackproof with (n:=n1) (s:=s) (r:=base_round) (ackp:=ackp). auto. auto. auto. 
    split. auto. lia. 

    intros.
    assert (round1 = base_round) as Hround1. lia.
    

    assert (first_rcvd_lp n2 s round1 = Some lp1) as Hf_rcv.
    apply ack_only_if_first_rcv_lp with (s:=s) (n:=n2) (r:=round1) (lp:=lp1). auto. auto. auto. 

    assert (lp1 = lp) as Hlp1.
    replace round1 with lp.(lp_round) in Hf_rcv by lia.
    apply important_lemma with (s:=s) (n:=n) (n2:=n2) (lp:=lp) (lp1:=lp1). all:auto. rewrite Hlp1. auto.

    (* induction step *)
    destruct IHr_gap as [IH_lock_ackp IH_hack].
    split.
    intros.
    (* lock ackp *)
    assert (exists ackp: AckpT, highest_locked_ackproof n1 s (base_round+r_gap) = Some ackp /\ ackp_ap ackp = lp_ap lp /\ ackp_round ackp >= base_round) as Hackp_cons.
    apply IH_lock_ackp with (n1:=n1). auto. auto. 
    destruct Hackp_cons as [ackp [Hhlock_ackp [Hackp_ap Hackp_round]]].

    replace (base_round + S r_gap) with ((base_round +r_gap + 1)) by lia.
    apply important_lemma_across_rounds_helper2. all:auto.

    intros.
    assert ({round1 <= base_round + r_gap} + {round1 > base_round+r_gap}).
    apply le_gt_dec.
    destruct H8.
    
    2:{apply important_lemma_across_rounds_helper1 with (s:=s)(lp:=lp)(r_gap:=r_gap)(n3:=n2)(lp3:=lp1). all:auto. 
    assert (round1 = base_round + r_gap+1) by lia.
    fold base_round.
    rewrite <- H8. auto.
    }

    apply IH_hack with (round1:= round1) (n2:=n2)(lp1:=lp1). all:auto.

Qed.
    

(* if an honest node certifies a lp in round r, then in future rounds, no honest nodes ack different ap.  *)
(* inference chain: (1) all locks on *)
Lemma important_lemma_across_rounds:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n:node, forall lp: LPT,
    is_honest_node n ->
    in_committee_for n s n ->
    certified_bk n s lp.(lp_round) = Some lp ->
    forall round1:nat, round1>=lp.(lp_round) ->
    forall n1: node, is_honest_node n1 -> (* saved the ack-witness in round lp_round *)
    in_committee_for n1 s n1 ->
    
    (forall lp1:LPT, acked_lp n1 s round1 = Some lp1 -> lp1.(lp_ap) = lp.(lp_ap)) /\
    (exists ackp, highest_locked_ackproof n1 s round1 = Some ackp /\ ackp.(ackp_ap) = lp.(lp_ap) /\ ackp.(ackp_round) >= lp.(lp_round)).

   (* start of proof *)

    intros.
    remember (round1-lp_round lp ) as r_gap.
    assert (round1 = lp_round lp + r_gap) by lia.
    rewrite H6.
    split.
    intros.
    apply important_lemma_across_rounds_helper_ultra with (s:=s) (n:=n)(lp:=lp)(r_gap:=r_gap)(round1:=lp.(lp_round) + r_gap)(n2:=n1). all:auto. lia.

    apply important_lemma_across_rounds_helper_ultra with (s:=s) (n:=n)(lp:=lp)(r_gap:=r_gap)(n1:=n1). all:auto.
Qed. 

(* proof-chain: enter slot sync -> receive honest winner sync -> ! not required in safety, only required in liveness. *)

(* as long as every committee member of slot s, enters slot s with at most delta delay among each other, confirming on the same bk in slot s-1 -> every node, will confirm the same bk in slot s. With delta delay. *)
Lemma safety_per_slot_helper:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n1 n2:node, forall bk1 bk2: FBkT,
    is_honest_node n1 -> is_honest_node n2 ->
    confirmed_bk n1 s = Some bk1 ->
    confirmed_bk n2 s = Some bk2 ->
    let lp1:= bk1.(bk_lp) in
    let lp2:= bk2.(bk_lp) in
    lp1.(lp_round) <= lp2.(lp_round) ->
    bk_equal bk1 bk2.

    intros. 
    inversion H2. 
    assert (exists com:node, is_honest_node com /\ in_committee_for com s n1 /\ let lp1:= bk1.(bk_lp) in certified_bk com s lp1.(lp_round) = Some lp1).
    apply confirm_implies_honest_certify with (s:=s) (n:=n1). auto. auto.
    destruct H5 as [com_node].
    destruct H5 as [H5_1 [H5_2 H5_3]].

    simpl in H5_3.

    inversion H5_3.

    assert (in_committee_for com_node s com_node) as Hincom.
    apply bk_implies_committee_view_pair_equal with (s:=s) (com:=com_node) (n1:=n1)(n2:=com_node). auto. auto. auto. auto. 

    apply important_lemma with (s:=s) (n:=com_node) (lp:=lp1) in H7. 2:auto. 2:auto. 2:auto.

    destruct H7 as [H7_1 H7_2].

    (* n2->bk2. for same slot, h2 cert->h2 acked. lp2=lp1 *)
    inversion H3.
    assert (exists com:node, is_honest_node com /\ in_committee_for com s n2 /\ let lp:= bk2.(bk_lp) in certified_bk com s lp.(lp_round) = Some lp).
    apply confirm_implies_honest_certify with (s:=s) (n:=n2). auto. auto.
    destruct H5 as [com_node2].
    destruct H5 as [H8_1 [H8_2 H8_3]].
    simpl in H8_3.

    remember (lp2.(lp_round)-lp1.(lp_round)) as r_gap.
    assert (lp2.(lp_round) = lp1.(lp_round) + r_gap) by lia.


    

    assert (in_committee_for com_node2 s com_node2).
    apply bk_implies_committee_view_pair_equal with (s:=s) (com:=com_node2) (n1:=n2)(n2:=com_node2). auto. auto. auto. auto.

    (* com_node1/2 certs => also acked. *)


    assert(acked_lp com_node2 s lp2.(lp_round) = Some lp2).
    apply honest_cert_implies_honest_ack with (s:=s) (r:=lp2.(lp_round)) (lp:=lp2). auto. auto. auto. auto.

    specialize H7_2 with (n2:=com_node2).

    assert (forall lp3:LPT, acked_lp com_node2 s lp1.(lp_round) = Some lp3 -> lp3 = lp1).
    intros.
    assert (first_rcvd_lp com_node2 s lp1.(lp_round) = Some lp3).
    apply ack_only_if_first_rcv_lp with (n:=com_node2) (s:=s) (r:=lp1.(lp_round)). auto. auto. auto. auto.

    
    destruct_with_eqn r_gap.
    (* in the same slot, no-one certifies a different bk *)
    assert (lp_round lp2 = lp_round lp1) by lia.
    pose proof H10 as H10'.
    rewrite <-H11 in H10'.
    rewrite H9 in H10'.
    assert (lp2 = lp1).
    apply H10'. auto. 
    unfold bk_equal.
    unfold fb2aggbk.
    unfold lp1 in H12.
    unfold lp2 in H12.
    rewrite H12.
    auto.

    apply important_lemma_across_rounds with (s:=s) (n:=com_node) (n1:=com_node2) (lp:=lp1) (round1:=lp2.(lp_round)) (lp1:=lp2) in H5_3. 
    unfold bk_equal. unfold fb2aggbk. unfold lp1 in H5_3. unfold lp2 in H5_3. auto. 

    auto. auto. auto. lia. auto. auto. auto.
Qed.

Lemma safety_per_slot:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n1 n2:node, forall bk1 bk2: FBkT,
    is_honest_node n1 -> is_honest_node n2 ->
    confirmed_bk n1 s = Some bk1 ->
    confirmed_bk n2 s = Some bk2 ->
    bk_equal bk1 bk2.
    intros.
    remember (bk1.(bk_lp)) as lp1.
    remember (bk2.(bk_lp)) as lp2.

    assert ({lp1.(lp_round) <= lp2.(lp_round)} + {lp2.(lp_round)<lp1.(lp_round)}).
    apply le_lt_dec.

    destruct H4.
    apply safety_per_slot_helper with (s:=s)(n1:=n1)(n2:=n2)(bk1:=bk1)(bk2:=bk2). auto. auto. auto. auto. auto. rewrite <- Heqlp1. rewrite <-Heqlp2. auto.


    assert (bk_equal bk2 bk1).
    apply safety_per_slot_helper with (s:=s)(n1:=n2)(n2:=n1)(bk1:=bk2)(bk2:=bk1). auto. auto. auto. auto. auto. rewrite <- Heqlp2. rewrite <-Heqlp1. lia.
    unfold bk_equal. unfold bk_equal in H4. auto.

Qed.



Lemma start_r0_after_interact:
    forall n:node, forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    is_honest_node n ->
    in_committee_for n s n ->
        start_round_time n s 0 = enter_slot_time n s + interact_duration. 
Admitted. 

Lemma each_round_time_bound:
    forall n:node, forall s:slot, forall r:nat,
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    is_honest_node n ->
    in_committee_for n s n ->
        start_round_time n s r <= leave_round_time n s r /\ leave_round_time n s r <= start_round_time n s r + round_duration. 
Admitted. 

Lemma next_round_time_bound: (* todo fix the time. *)
    forall n:node, forall s:slot, forall r:nat,
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    is_honest_node n ->
    in_committee_for n s n -> 
        start_round_time n s (S r) >= leave_round_time n s r /\ start_round_time n s (S r) <= leave_round_time n s r + 3*delta.
Admitted. 


Lemma last_round_confirm:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n:node, forall last_r:nat, 
    is_honest_node n ->
    in_committee_for n s n ->
    last_round n s = Some last_r ->
    exists fb: FBkT, confirmed_bk n s = Some fb /\ confirm_slot_time n s <= enter_slot_time n s + (last_r+1)*round_duration.
Admitted. 



Lemma confirm_or_quit:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n:node, forall r:nat,
    is_honest_node n ->
    in_committee_for n s n ->
    ~has_confirmed_in_slot_round n s r -> 
    exists qt: QuiT, quit_round_proof n s r = Some qt.
Admitted. 

(* quit round time is leave round time. 
    by confirm, also leaves round, but is not quitting round. 
*)
Lemma one_quit_other_quit:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n1 n2:node, forall r:nat,
    is_honest_node n1 -> is_honest_node n2 ->
    in_committee_for n1 s n1 -> in_committee_for n2 s n2 ->
    forall qt1:QuiT,
    quit_round_proof n1 s r = Some qt1 ->
    exists qt2: QuiT, quit_round_proof n2 s r = Some qt2.
Admitted. 

Lemma h_leader_rcv_r0:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n_l:node,
    is_honest_node n_l ->
    in_committee_for n_l s n_l ->
    local_committee_leader_order n_l s n_l = 0 ->
    exists lp:LPT, 
    forall n:node, is_honest_node n -> in_committee_for n s n ->
    first_rcvd_lp n s 0 = Some lp.
Admitted. 

Lemma h_leader_not_confirm_will_send_lp:
    forall s:slot,
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall r:nat, forall n_l:node,
    r < n_committee ->
    is_honest_node n_l ->
    in_committee_for n_l s n_l ->
    local_committee_leader_order n_l s n_l = r ->
    ~has_confirmed_in_slot_round n_l s r ->
    (exists lp:LPT,
        forall n:node, is_honest_node n -> in_committee_for n s n ->
        has_confirmed_in_slot_round n s r \/ first_rcvd_lp n s r = Some lp).
Admitted. 

(* when the leader is honest, rcvd lp -> ack lp *)
Lemma h_leader_rcv_will_ack:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall r:nat, forall n_l:node, forall lp:LPT, forall n:node, 
    r < n_committee ->
    is_honest_node n_l ->
    in_committee_for n_l s n_l ->
    local_committee_leader_order n_l s n_l = r ->
    is_honest_node n -> in_committee_for n s n ->
    first_rcvd_lp n s r = Some lp ->
    acked_lp n s r = Some lp. 

Admitted. 


Lemma h_leader_ack_will_confirm:
    forall s:slot,
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall r:nat, forall n_l:node, forall lp:LPT, 
    r < n_committee ->
    is_honest_node n_l ->
    in_committee_for n_l s n_l ->
    local_committee_leader_order n_l s n_l = r ->
    (forall n:node, is_honest_node n ->
    in_committee_for n s n ->
    first_rcvd_lp n s r = Some lp
    ) -> (* requiring every honest com to rcv: they don't confirm before that. *)
    (forall n1:node, is_honest_node n1->
    in_committee_for n1 s n1 ->
    has_confirmed_in_slot_round n1 s r
    ).
Admitted. 

Lemma has_confirmed_has_bk:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n:node, forall r:nat,
    is_honest_node n->
    in_committee_for n s n ->
    has_confirmed_in_slot_round n s r ->
    exists bk: FBkT, confirmed_bk n s = Some bk.

Admitted. 

(* proof sketch: 
    1. in every slot (committee), there is at least one honest leader. In his view. 
    2. if there is any ackp, He receives all locked cert from honest nodes. His prp will be acked by every honest node. & timer starts & no duplicate, no blame & ackp reaches every honest node on time, & all honest cert -> confirm. 
    3. if there is no ackp (by honest nodes). Then the leader must have received the ap of highest weight among honest nodes. Same reasoning applies. 

    considering time: 
    1. the first leader should start working at some time. 
    2. for every 2\delta, if nothing happens, the leader is changed. 
    3. if not receiving f+1 cert, the new leader will actually send prps. 
    3. therefore, if 
*)
Lemma liveness_per_slot:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall n:node, is_honest_node n -> 
    (exists bk: FBkT,
    confirmed_bk n s = Some bk) /\ confirm_slot_time n s <= enter_slot_time n s + slot_duration + 2*delta.

    (*begin of proof*)
    intros. 
    assert (exists n_hc:node, in_committee_for n_hc s n_hc /\ is_honest_node n_hc /\ local_committee_leader_order n_hc s n_hc < n_committee).
    apply exists_honest_com_node with (s:=s). auto.
     
    destruct H1 as [n_hc [H_hc_c [H_hc_h H_hc_order]]].

    (* either all confirmed, or all not confirmed. However, confirmation time not linked with rounds yet. *)
    (* two cases by H_hc_order *)
    remember (local_committee_leader_order n_hc s n_hc) as hc_order. 
    destruct_with_eqn hc_order.

    (* in round 0 
        first: assert rcv 
    *)
    assert (exists lp:LPT, forall n:node, is_honest_node n -> in_committee_for n s n -> first_rcvd_lp n s 0 = Some lp).
    apply h_leader_rcv_r0 with (s:=s) (n_l:=n_hc). all:auto. 

    destruct H1 as [lp Hlp].

    assert (forall n:node, is_honest_node n -> in_committee_for n s n ->
    acked_lp n s 0 = Some lp). 

    intros.
    assert (first_rcvd_lp n0 s 0 =Some lp). apply Hlp with (n:=n0). auto. auto.
    apply h_leader_rcv_will_ack with (s:=s) (r:=0) (n_l:=n_hc) (lp:=lp) (n:=n0). all:auto. 

    assert (forall n1:node, is_honest_node n1 -> in_committee_for n1 s n1 ->
    has_confirmed_in_slot_round n1 s 0). 
    apply h_leader_ack_will_confirm with (s:=s) (r:=0) (n_l:=n_hc) (lp:=lp). all:auto. 

    assert (has_confirmed_in_slot_round n_hc s 0).
    apply H2 with (n1:=n_hc). all:auto. 

    (* confirmed -> bk *)
    assert(exists bk: FBkT, confirmed_bk n_hc s = Some bk).
    apply has_confirmed_has_bk with (s:=s) (n:=n_hc) (r:=0). all:auto.

    (* com node confirms in round -> non-com node also confirm soon *)
    destruct H4 as [bk Hbk].

    pose proof Hbk as Hbk_tmp. 
    apply one_confirm_other_confirm_noncom with (s:=s) (n1:=n_hc) (n2:=n) (b1:=bk) in Hbk_tmp. all:auto.
    destruct Hbk_tmp as [bk2 [Hc_b2 [Heql_b1_b2 Hb2_conf_time]]].
    split. exists bk2. auto.
    apply com_confirm_time with (s:=s)(n:=n_hc)(r:=0) in H3. all:auto. 
    assert (enter_slot_time n_hc s <= enter_slot_time n s + delta).  apply enter_slot_time_diff with (s:=s)(n1:=n_hc)(n2:=n). all:auto. 
    unfold slot_duration. 
    lia. 

    (* now in case r>0 | either has_confirmed or not *)
    assert (has_confirmed_in_slot_round n_hc s hc_order \/ ~has_confirmed_in_slot_round n_hc s hc_order).
    apply classic.

    destruct H1 as [H_has_confed | H_not_confed].
    (* in case has confirmed -> the other will confirm *)
    assert (exists bk: FBkT, confirmed_bk n_hc s = Some bk).
    apply has_confirmed_has_bk with (s:=s) (n:=n_hc) (r:=hc_order). all:auto.

    destruct H1 as [bk Hbk].
    pose proof Hbk as Hbk_tmp.
    apply one_confirm_other_confirm_noncom with (s:=s) (n1:=n_hc) (n2:=n) (b1:=bk) in Hbk_tmp. all:auto.
    destruct Hbk_tmp as [bk2 [Hc_b2 [Heql_b1_b2 Hb2_conf_time]]].
    split. exists bk2. auto.
    apply com_confirm_time with (s:=s)(n:=n_hc)(r:=hc_order) in H_has_confed. all:auto.
    assert (enter_slot_time n_hc s <= enter_slot_time n s + delta).  apply enter_slot_time_diff with (s:=s)(n1:=n_hc)(n2:=n). all:auto.
    unfold slot_duration.
    nia. (* because of multiply, lia does not work: n_c*round_duration *)

    (* in case not confirmed *)
    assert (exists lp:LPT,
        forall n:node, is_honest_node n -> in_committee_for n s n ->
        has_confirmed_in_slot_round n s hc_order \/ first_rcvd_lp n s hc_order = Some lp) as H_other.
    apply h_leader_not_confirm_will_send_lp with (s:=s) (r:=hc_order) (n_l:=n_hc). all:auto. lia. rewrite Heqn0. auto.
    destruct H_other as [lp H_other].
    (* want case analysis: (1) all honest com not confirm. (2) some honest com confirmed*)
    assert ((exists n1:node, is_honest_node n1 /\ in_committee_for n1 s n1 /\ has_confirmed_in_slot_round n1 s hc_order) \/ ~(exists n1:node, is_honest_node n1 /\ in_committee_for n1 s n1 /\ has_confirmed_in_slot_round n1 s hc_order) ).
    apply classic.
    destruct H1.
    destruct H1 as [n1 [Hn1 [Hn1_c Hn1_conf]]].
    assert (exists bk: FBkT, confirmed_bk n1 s = Some bk).
    apply has_confirmed_has_bk with (s:=s) (n:=n1) (r:=hc_order). all:auto.
    destruct H1 as [bk Hbk].
    pose proof Hbk as Hbk_tmp.
    apply one_confirm_other_confirm_noncom with (s:=s) (n1:=n1) (n2:=n) (b1:=bk) in Hbk_tmp. all:auto.
    destruct Hbk_tmp as [bk2 [Hc_b2 [Heql_b1_b2 Hb2_conf_time]]].
    split. exists bk2. auto.
    apply com_confirm_time with (s:=s)(n:=n1)(r:=hc_order) in Hn1_conf. all:auto. unfold slot_duration. 

    assert (enter_slot_time n1 s <= enter_slot_time n s + delta).  apply enter_slot_time_diff with (s:=s)(n1:=n1)(n2:=n). all:auto.
    nia. 

    (* in case no honest com confirmed *)
    assert (forall n1:node, ~(is_honest_node n1 /\ in_committee_for n1 s n1 /\ has_confirmed_in_slot_round n1 s hc_order)).
    apply not_ex_all_not. auto.
    assert (forall n:node, is_honest_node n -> in_committee_for n s n -> first_rcvd_lp n s hc_order = Some lp).
    intros. 
    assert (has_confirmed_in_slot_round n1 s hc_order \/ first_rcvd_lp n1 s hc_order = Some lp). apply H_other. auto. auto.
    destruct H5.
    assert (~(is_honest_node n1 /\ in_committee_for n1 s n1 /\ has_confirmed_in_slot_round n1 s hc_order)).
    apply H2.
    assert (is_honest_node n1 /\ in_committee_for n1 s n1 /\ has_confirmed_in_slot_round n1 s hc_order).
    auto. 
    congruence.
    auto.

    (* now proved every hcom rcved -> will ack -> will confirm *)
    assert (has_confirmed_in_slot_round n_hc s hc_order).
    apply h_leader_ack_will_confirm with (s:=s) (r:=hc_order) (n_l:=n_hc) (lp:=lp). all:auto. lia. rewrite Heqn0. auto. 

    assert (~(is_honest_node n_hc /\ in_committee_for n_hc s n_hc /\ has_confirmed_in_slot_round n_hc s hc_order)).
    apply H2. auto. auto. auto.
    congruence.
    (* now n_hc confirmed -> all confirmed *)
    (* confirmed -> bk *) 
Qed.

Lemma safety_helper:
    forall s:slot,
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    confirm_same_bk_pred s. 
    intros.
    unfold confirm_same_bk_pred.
    assert (exists n_hc:node, in_committee_for n_hc s n_hc /\ is_honest_node n_hc /\ local_committee_leader_order n_hc s n_hc < n_committee).
    apply exists_honest_com_node with (s:=s). auto.
    destruct H0 as [n_hc [H_hc_c [H_hc_h H_hc_order]]].

    
    assert (exists bk:FBkT, confirmed_bk n_hc s = Some bk).
    apply liveness_per_slot with (s:=s). auto. auto.
    destruct H0 as [bk Hbk].
    exists bk.(bk_lp).(lp_ap). intros.
    assert (exists bk2:FBkT, confirmed_bk n s = Some bk2 /\ bk_equal bk bk2 /\ confirm_slot_time n s <= confirm_slot_time n_hc s + delta ).
    apply one_confirm_other_confirm_noncom with (s:=s) (n1:=n_hc) (n2:=n) (b1:=bk). all:auto.
    destruct H1 as [bk2 [Hc_b2 [Heql_b1_b2 Hb2_conf_time]]].
    exists bk2. split. auto. 
    unfold bk_equal in Heql_b1_b2. unfold fb2aggbk in Heql_b1_b2. auto.

Qed.

Lemma safety_real:
    forall s:slot, 
        confirm_same_bk_pred s.
    intros.
    induction s.
    apply safety_helper. left. auto.
    apply safety_helper. right. replace (S s-1) with s by lia. auto.
Qed.

(* safety theorem: *)
Theorem safety: 
    forall s:slot, forall n1 n2:node, forall bk1 bk2: FBkT,
    is_honest_node n1 -> is_honest_node n2 ->
    confirmed_bk n1 s = Some bk1 ->
    confirmed_bk n2 s = Some bk2 ->
    bk_equal bk1 bk2.
    intros.
    assert (confirm_same_bk_pred s).
    apply safety_real.
    unfold confirm_same_bk_pred in H3.
    destruct H3 as [ap Hap].
    unfold bk_equal.
    apply Hap in H. destruct H as [bk1' [Hb1 Hb1ap]].
    apply Hap in H0. destruct H0 as [bk2' [Hb2 Hb2ap]].
    rewrite Hb1 in H1. inversion H1. destruct H1. 
    rewrite Hb2 in H2. inversion H2. destruct H2.
    rewrite H0 in Hb1ap. rewrite H1 in Hb2ap.  
    rewrite Hb1ap. rewrite Hb2ap. auto.
Qed.


(* liveness theorem: *)
Theorem liveness:
    forall s:slot, forall n:node, 
    is_honest_node n -> 
        (exists bk: FBkT, 
        confirmed_bk n s = Some bk) /\ confirm_slot_time n s <= enter_slot_time n s + slot_duration+2*delta.
    intros.
    
    induction s. 
    apply liveness_per_slot with (s:=0)(n:=n). left. auto. auto. 

    assert (confirm_same_bk_pred s).
    apply safety_real.
    apply liveness_per_slot with (s:=S s)(n:=n). right. replace (S s - 1) with s by lia. auto. auto. 
    
Qed. 

Lemma honest_ack_only_if_larger_weight_s0:
    forall r:nat, forall n:node, forall lp:LPT,
    is_honest_node n ->
    in_committee_for n 0 n ->
    acked_lp n 0 r = Some lp ->
    (r = 0 -> lp.(lp_ap).(ap_weight) >= (local_winner_s0 n).(ap_weight)) /\
    (r >= 1 -> 
    let o_locked:= highest_locked_ackproof n 0 (r-1) in
    (forall locked:AckpT, o_locked=Some locked -> (
        exists ackp:AckpT, lp.(lp_ackp) = Some ackp /\
        ackp.(ackp_round) >= locked.(ackp_round)
    )) /\
    (o_locked = None -> (
        exists ackp:AckpT, lp.(lp_ackp) = Some ackp 
    ) \/ (lp.(lp_ackp) = None /\ lp.(lp_ap).(ap_weight) >= (local_winner_s0 n).(ap_weight)))
    ).
Admitted.

Lemma honest_acked_lp_cert_from_previous_round:
    forall s:slot,
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall r:nat, forall n:node, forall lp:LPT, forall ackp:AckpT,
    is_honest_node n ->
    in_committee_for n s n ->
    acked_lp n s (S r) = Some lp ->
    lp.(lp_ackp) = Some ackp ->
    ackp.(ackp_round) <= r.
Admitted.  

Lemma honest_acked_lp_cert_same_ap:
    forall s:slot,
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall r:nat, forall n:node, forall lp:LPT, forall ackp:AckpT,
    is_honest_node n ->
    in_committee_for n s n ->
    acked_lp n s (S r) = Some lp ->
    lp.(lp_ackp) = Some ackp ->
    lp.(lp_ap) = ackp.(ackp_ap).
Admitted.


Lemma honest_ack_only_if_larger_weight_or_ackp_s1:
    forall s:slot, forall prev_ap:AggT, 
    (forall n:node, is_honest_node n -> exists bk:FBkT, confirmed_bk n s = Some bk /\ fb2aggbk bk = prev_ap) ->
    forall r:nat, forall n2:node, forall lp:LPT,
    is_honest_node n2 ->
    in_committee_for n2 (S s) n2 ->
    acked_lp n2 (S s) r = Some lp ->
    (r = 0 -> lp.(lp_ap).(ap_weight) >= prev_ap.(ap_weight)) /\
    (r >= 1 -> 
    let o_locked:= highest_locked_ackproof n2 (S s) (r-1) in
    (forall locked:AckpT, o_locked=Some locked -> (
        exists ackp:AckpT, lp.(lp_ackp) = Some ackp /\
        ackp.(ackp_round) >= locked.(ackp_round)
    ) /\ (o_locked = None -> (
        exists ackp:AckpT, lp.(lp_ackp) = Some ackp 
    ) \/ (lp.(lp_ackp) = None /\ lp.(lp_ap).(ap_weight) >= prev_ap.(ap_weight)))
    )
    ).

Admitted. 

Lemma h_acked_lp_cert_implies_h_ack:
    forall s:slot, 
    (s = 0 \/ confirm_same_bk_pred (s-1)) ->
    forall r:nat, forall n:node, forall lp:LPT, forall ackp:AckpT, 
    is_honest_node n ->
    in_committee_for n s n ->
    acked_lp n s (S r) = Some lp ->
    lp.(lp_ackp) = Some ackp ->
    exists n_h:node, exists prev_lp:LPT, is_honest_node n_h /\ in_committee_for n_h s n_h /\ acked_lp n_h s ackp.(ackp_round) = Some prev_lp /\ prev_lp.(lp_ap) = ackp.(ackp_ap) /\ ackp.(ackp_round) = prev_lp.(lp_round).
Admitted. 
    

Lemma honest_ack_only_if_at_least_hw_s0:
    forall r r1:nat, forall n:node, forall lp:LPT, 
    is_honest_node n ->
    in_committee_for n 0 n ->
    r1<= r ->
    acked_lp n 0 r1 = Some lp ->
    lp.(lp_ap).(ap_weight) >= honest_winner_s0.(ap_weight).

    (* require strong induction on r *)
    intro r.
    induction r.

    intros.
    assert (r1 = 0) by lia.
    replace r1 with 0. replace r1 with 0 in H2. clear H1 H3 r1.
    apply honest_ack_only_if_larger_weight_s0 with (r:=0) (n:=n) (lp:=lp) in H. all:auto.
    destruct H as [H_r0 H_r1].
    assert (ap_weight (lp_ap lp) >= ap_weight (local_winner_s0 n)). auto.
    assert (ap_weight (local_winner_s0 n) >= ap_weight (honest_winner_s0)). apply local_winner_s0_at_least_high_as_honest. lia.

    (* r>=1*)
    intros.
    assert (r1 <= r \/ r1 =  S r) by lia.
    destruct H3.
    apply IHr with (r1:=r1)(n:=n)(lp:=lp). all:auto.

    (* r1 = S r *)

    rewrite H3 in H2. clear  H1 H3 r1.

    pose proof H2 as H2_tmp.
    apply honest_ack_only_if_larger_weight_s0 with (r:=S r) (n:=n) (lp:=lp) in H2_tmp. all:auto.
    replace (S r -1) with r in H2_tmp by lia.
    destruct H2_tmp as [H_r0 H_r1].

    assert (S r>=1) as Htmp by lia.
    destruct_with_eqn (highest_locked_ackproof n 0 r).
    (* prev locked *)
    apply H_r1 with (locked:=a) in Htmp. all:auto.

    destruct Htmp as [ackp [Hc1_1 Hc1_2]].

    pose proof Hc1_1 as Hc1_1_tmp.
    apply h_acked_lp_cert_implies_h_ack with (s:=0) (r:=r) (n:=n) (lp:=lp) (ackp:=ackp) in Hc1_1_tmp. all:auto.
    destruct Hc1_1_tmp as [n_h [prev_lp [Hc1_1_1 [Hc1_1_2 [Hc1_1_3 [Hc1_1_4 Hc1_1_5]]]]]].

    (* ackp_round < lp round*)
    assert (ackp.(ackp_round) <= r).
    apply honest_acked_lp_cert_from_previous_round with (s:=0) (r:=r) (n:=n) (lp:=lp) (ackp:=ackp). all:auto.    

    assert (ap_weight (lp_ap prev_lp)>=ap_weight honest_winner_s0).
    apply IHr with (r1:=ackp.(ackp_round))(n:=n_h)(lp:=prev_lp). all:auto.

    assert (lp.(lp_ap) = ackp.(ackp_ap)).
    apply honest_acked_lp_cert_same_ap with (s:=0) (r:=r) (n:=n) (lp:=lp) (ackp:=ackp). all:auto.
    rewrite H4. 
    rewrite <- Hc1_1_4. auto.

    (* prev not locked. *)
    assert ((exists ackp:AckpT, lp_ackp lp = Some ackp) \/ (lp_ackp lp = None /\ ap_weight (lp_ap lp) >= ap_weight (local_winner_s0 n))).
    apply H_r1  in Htmp. auto.
    destruct Htmp as [_ Hp2].
    apply Hp2. auto.

    (* two cases. *)
    destruct H1.
    1:{
    destruct H1 as [ackp Hackp].
    (* now the lp has cert | similar to above *)

    pose proof Hackp as Hc1_1_tmp.
    apply h_acked_lp_cert_implies_h_ack with (s:=0) (r:=r) (n:=n) (lp:=lp) (ackp:=ackp) in Hc1_1_tmp. all:auto.

    destruct Hc1_1_tmp as [n_h [prev_lp [Hc1_1_1 [Hc1_1_2 [Hc1_1_3 [Hc1_1_4 Hc1_1_5]]]]]].

    assert (ackp.(ackp_round) <= r).
    apply honest_acked_lp_cert_from_previous_round with (s:=0) (r:=r) (n:=n) (lp:=lp) (ackp:=ackp). all:auto.    

    assert (ap_weight (lp_ap prev_lp)>=ap_weight honest_winner_s0).
    apply IHr with (r1:=ackp.(ackp_round))(n:=n_h)(lp:=prev_lp). all:auto.

    assert (lp.(lp_ap) = ackp.(ackp_ap)).
    apply honest_acked_lp_cert_same_ap with (s:=0) (r:=r) (n:=n) (lp:=lp) (ackp:=ackp). all:auto.
    rewrite H4. 
    rewrite <- Hc1_1_4. auto. 
    }

    destruct H1 as [H1 Hw].
    assert (ap_weight (local_winner_s0 n) >= ap_weight (honest_winner_s0)).
    apply local_winner_s0_at_least_high_as_honest. lia.
Qed.



Lemma honest_ack_only_if_at_least_hw_s1:
    forall s:slot, 
    forall r r1:nat, forall n:node, forall lp:LPT, forall bk:FBkT,
    confirmed_bk n s = Some bk ->
    is_honest_node n ->
    in_committee_for n (S s) n ->
    r1 <= r ->
    acked_lp n (S s) r = Some lp ->
    lp.(lp_ap).(ap_weight) >= (honest_winner (S s) (fb2aggbk bk)).(ap_weight).
    
Admitted. 

Lemma confirm_same_bk_helper:
    forall s:slot,
    confirm_same_bk_pred s ->
        forall n1 n2:node, forall bk1:FBkT,
        is_honest_node n1 -> is_honest_node n2 ->
        confirmed_bk n1 s = Some bk1 ->
        exists bk2:FBkT, confirmed_bk n2 s = Some bk2 /\ fb2aggbk bk1 = fb2aggbk bk2.
    intros.

    unfold confirm_same_bk_pred in H.
    destruct H as [ap Hap].
    apply Hap in H0. destruct H0 as [bk1' [Hb1 Hb1ap]].
    apply Hap in H1. destruct H1 as [bk2' [Hb2 Hb2ap]].
    rewrite Hb1 in H2. inversion H2. destruct H2.
    exists bk2'. 
    split. auto.
    rewrite Hb2ap. rewrite <- H0.
    auto.
Qed.

Theorem democracy:
    forall s:slot, forall n:node, 
    is_honest_node n ->
    forall bk:FBkT, 
    confirmed_bk n s = Some bk ->
    (s = 0 ->
    bk.(bk_lp).(lp_ap).(ap_weight) >= honest_winner_s0.(ap_weight)) /\
    (s > 0 -> exists prev_bk:FBkT, confirmed_bk n (s-1) = Some prev_bk -> bk.(bk_lp).(lp_ap).(ap_weight) >= (honest_winner s (prev_bk.(bk_lp).(lp_ap))).(ap_weight)).

    intros.

    assert (s = 0 \/ confirm_same_bk_pred (s-1)) as Hsame.
    destruct_with_eqn s. left. auto. right.
    replace (S s0 - 1) with s0 by lia.
    apply safety_real.

    split.
    intros.

    (* h confirmed -> h2 certed -> h2 acked. *)
    rewrite H1 in H0.

    assert (exists com:node, is_honest_node com /\ in_committee_for com 0 n /\ let lp:=bk.(bk_lp) in certified_bk com 0 lp.(lp_round) = Some lp).

    apply confirm_implies_honest_certify with (s:=0) (n:=n) (fb:=bk). all:auto. 

    destruct H2 as [com [Hcom [Hcom_c Hcom_cert]]].
    simpl in Hcom_cert.
    assert (in_committee_for com 0 com).
    apply bk_implies_committee_view_pair_equal with (s:=0)(com:=com)(n1:=n)(n2:=com). all:auto. 
    assert (acked_lp com 0 (bk.(bk_lp).(lp_round)) = Some bk.(bk_lp)).
    apply honest_cert_implies_honest_ack with (s:=0)(n:=com)(lp:=bk.(bk_lp)). all:auto.
    apply honest_ack_only_if_at_least_hw_s0 with (r:=bk.(bk_lp).(lp_round))(r1:=bk.(bk_lp).(lp_round))(n:=com)(lp:=bk.(bk_lp)). all:auto.

    (* s>0 *)
    intros.
    pose proof Hsame as Htmp.
    destruct Htmp. lia.
    unfold confirm_same_bk_pred in H2.
    destruct H2 as [ap Hap].
    assert (exists prev_bk:FBkT, confirmed_bk n (s-1) = Some prev_bk /\ fb2aggbk prev_bk = ap).
    apply Hap with (n:=n). auto.
    destruct H2 as [prev_bk [Hprev_bk Hprev_bk_ap]].
    exists prev_bk.
    intros.

    assert (exists com:node, is_honest_node com /\ in_committee_for com s n /\ let lp:=bk.(bk_lp) in certified_bk com s lp.(lp_round) = Some lp).

    apply confirm_implies_honest_certify with (s:=s) (n:=n) (fb:=bk). all:auto. 

    destruct H3 as [com [Hcom [Hcom_c Hcom_cert]]].
    simpl in Hcom_cert.
    assert (in_committee_for com s com).
    apply bk_implies_committee_view_pair_equal with (s:=s)(com:=com)(n1:=n)(n2:=com). all:auto. 
    assert (acked_lp com s (bk.(bk_lp).(lp_round)) = Some bk.(bk_lp)).
    apply honest_cert_implies_honest_ack with (s:=s)(n:=com)(lp:=bk.(bk_lp)). all:auto.

    assert (confirm_same_bk_pred s).
    apply safety_real.
    unfold confirm_same_bk_pred in H5.
    destruct H5 as [new_ap Hnew_ap].
    assert (exists bk_n:FBkT, confirmed_bk n s = Some bk_n /\ fb2aggbk bk_n = new_ap).
    apply Hnew_ap with (n:=n). auto.
    destruct H5 as [bk_n [Hbk_n Hbk_n_ap]].
    assert (bk_n = bk). rewrite H0 in Hbk_n. inversion Hbk_n. auto.
    assert (exists bk_com:FBkT, confirmed_bk com s = Some bk_com /\ fb2aggbk bk_com = new_ap).
    apply Hnew_ap with (n:=com). auto.
    destruct H6 as [bk_com [Hbk_com Hbk_com_ap]].
    (* replace (lp_ap (bk_lp bk)) with (fb2aggbk bk). 2:{unfold fb2aggbk. auto. }
    rewrite <-H5. rewrite Hbk_n_ap.  
    rewrite <- Hbk_com_ap. 
    unfold fb2aggbk. *)

    (* also change prev_bk*)

    replace (lp_ap (bk_lp prev_bk)) with (fb2aggbk prev_bk).
    (* in s -1, n confirmed prev_bk, *)
    assert (exists prev_bk_com:FBkT, confirmed_bk com (s-1) = Some prev_bk_com /\ fb2aggbk prev_bk = fb2aggbk prev_bk_com).
    apply confirm_same_bk_helper with (s:=s-1)(n1:=n)(n2:=com)(bk1:=prev_bk). all:auto. apply safety_real.
    destruct H6 as [prev_bk_com [Hprev_bk_com Hprev_bk_com_ap]].
    rewrite Hprev_bk_com_ap. 
    replace s with (S (s-1)) by lia. 
    apply honest_ack_only_if_at_least_hw_s1 with (r:=bk.(bk_lp).(lp_round))(r1:=bk.(bk_lp).(lp_round))(n:=com)(lp:=bk.(bk_lp))(bk:=prev_bk_com)(s:=s-1). all:auto.
    all:replace (S (s-1)) with s by lia. auto. all:auto. 


Qed.

End ProofOfElection.