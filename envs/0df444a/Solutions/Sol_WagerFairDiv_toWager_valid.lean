-- Prove2me | solution 1 for WagerFairDiv.toWager_valid
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:02:09.266947+00:00
-- url     : https://prove2.me/submissions/8cbcab1e-e51e-400f-9426-f519ea76ed7b

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

open WagerFairDiv in
theorem solution {n m : ℕ} (A B : Mech n m) (hA : IsAllocMech A)
    (hAB : Corresponding A B) : IsWagerMech B ∧ WeaklyBB B := by
  have htot : ∀ w : PosVec n, 0 ≤ w.total := fun w =>
    Finset.sum_nonneg fun i _ => le_of_lt (w.2 i)
  refine ⟨fun p w i j => ?_, fun p w j => ?_⟩
  · rw [hAB]
    exact mul_nonneg (htot w) ((hA p w).1 i j)
  · simp_rw [hAB p w]
    rw [← Finset.mul_sum]
    calc w.total * ∑ i, A p w i j ≤ w.total * 1 :=
          mul_le_mul_of_nonneg_left ((hA p w).2 j) (htot w)
      _ = w.total := mul_one _
