-- Prove2me | solution 1 for WagerFairDiv.theorem_1_wager_of_alloc
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:47:07.804427+00:00
-- url     : https://prove2.me/submissions/a95640c7-a664-4c15-950b-de35e082a1e2

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

open WagerFairDiv in
theorem solution {n m : ℕ} (A B : Mech n m) (hAB : Corresponding A B) :
    (AllocWeakIC A → WagerWeakIC B) ∧ (AllocStrictIC A → WagerStrictIC B) := by
  have hval : ∀ p w i (x : Fin m → ℝ), val x (B p w i) = w.total * val x (A p w i) := by
    intro p w i x
    unfold val
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hAB]; ring
  have htot : ∀ (w : PosVec n) (i : Fin n), 0 < w.total := fun w i =>
    Finset.sum_pos (fun j _ => w.2 j) ⟨i, Finset.mem_univ i⟩
  have weak : AllocWeakIC A → WagerWeakIC B := by
    intro hA i pi p w
    rw [hval, hval]
    exact mul_le_mul_of_nonneg_left (hA i pi p w) (htot w i).le
  refine ⟨weak, fun hA => ⟨weak hA.1, fun i pi p w hne => ?_⟩⟩
  rw [hval, hval]
  exact mul_lt_mul_of_pos_left (hA.2 i pi p w hne) (htot w i)
