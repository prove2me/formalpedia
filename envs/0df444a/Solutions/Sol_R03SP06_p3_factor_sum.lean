-- Prove2me | solution 1 for R03SP06.p3_factor_sum
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:04:09.99435+00:00
-- url     : https://prove2.me/submissions/72c8f22a-2c29-47f4-87fd-464b864a7191

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP06

open CubicP3Partition

variable {A B : Type} [Fintype A] [Fintype B]


end R03SP06

open R03SP06
open CubicP3Partition
variable {A B : Type} [Fintype A] [Fintype B]
theorem solution
    {GA : SimpleGraph A} {GB : SimpleGraph B}
    (pA : P3Factor GA) (pB : P3Factor GB) :
    Nonempty (P3Factor (GA ⊕g GB)) := by
  let indexSplit :
      (Fin (pA.blockCount + pB.blockCount) × Fin 3) ≃
        (Fin pA.blockCount × Fin 3) ⊕ (Fin pB.blockCount × Fin 3) := by
    let e1 :
        (Fin (pA.blockCount + pB.blockCount) × Fin 3) ≃
          ((Fin pA.blockCount ⊕ Fin pB.blockCount) × Fin 3) :=
      Equiv.prodCongr finSumFinEquiv.symm (Equiv.refl (Fin 3))
    let e2 :
        ((Fin pA.blockCount ⊕ Fin pB.blockCount) × Fin 3) ≃
          (Fin pA.blockCount × Fin 3) ⊕ (Fin pB.blockCount × Fin 3) :=
      Equiv.sumProdDistrib (Fin pA.blockCount) (Fin pB.blockCount) (Fin 3)
    exact e1.trans e2
  let place :
      (Fin (pA.blockCount + pB.blockCount) × Fin 3) ≃ (A ⊕ B) :=
    indexSplit.trans (Equiv.sumCongr pA.place pB.place)
  refine ⟨{
    blockCount := pA.blockCount + pB.blockCount
    place := place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    let q : Fin pA.blockCount ⊕ Fin pB.blockCount := finSumFinEquiv.symm i
    have hq : finSumFinEquiv q = i := by
      dsimp [q]
      exact finSumFinEquiv.apply_symm_apply i
    rcases q with q | q
    · rw [← hq]
      simpa [place, indexSplit, Equiv.trans_apply, Equiv.prodCongr,
        Equiv.sumProdDistrib] using pA.edge01 q
    · rw [← hq]
      simpa [place, indexSplit, Equiv.trans_apply, Equiv.prodCongr,
        Equiv.sumProdDistrib] using pB.edge01 q
  · intro i
    let q : Fin pA.blockCount ⊕ Fin pB.blockCount := finSumFinEquiv.symm i
    have hq : finSumFinEquiv q = i := by
      dsimp [q]
      exact finSumFinEquiv.apply_symm_apply i
    rcases q with q | q
    · rw [← hq]
      simpa [place, indexSplit, Equiv.trans_apply, Equiv.prodCongr,
        Equiv.sumProdDistrib] using pA.edge12 q
    · rw [← hq]
      simpa [place, indexSplit, Equiv.trans_apply, Equiv.prodCongr,
        Equiv.sumProdDistrib] using pB.edge12 q

