# Coq Formalization of Proof of Election (PoE)

This repository contains the Coq formalization accompanying the paper:
**"Proof of Election: A Formally-Verified Democratic Blockchain Protocol"**
(Zhuo Cai and Amir Goharshady, IEEE DAPPS 2026).

## Contents

- `poe.v` — The complete Coq development (~2,800 lines). Contains the protocol model, 83 lemma/theorem statements, and mechanized proofs of safety, liveness, and democracy.

## Requirements

- [Coq](https://coq.inria.fr/) 8.18 or later (developed with 8.19)

## Checking the Proofs

```bash
coqc poe.v
```

This checks the entire development. The three top-level theorems (`safety`, `liveness`, `democracy`) are fully proved (end with `Qed`). Some supporting lemmas remain admitted; see the paper and the annotations in the file for details.

## Structure

The development is organized within `Section ProofOfElection` and covers:

- **Network model**: nodes, slots, committees, message passing with bounded synchrony
- **Protocol state machine**: proposal reception, voting, aggregation, committee certification (based on Sync HotStuff)
- **Safety**: no two honest nodes commit different blocks in the same slot
- **Liveness**: every honest node eventually commits a block in every slot
- **Democracy**: the committed block has at least as many votes as any honestly delivered candidate block

## Paper

The corresponding paper is available from the IEEE DAPPS 2026 proceedings.

## License

This project is provided for research and reproducibility purposes.
