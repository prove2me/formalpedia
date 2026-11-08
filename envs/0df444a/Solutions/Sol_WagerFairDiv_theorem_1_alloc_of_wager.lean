-- Prove2me | solution 1 for WagerFairDiv.theorem_1_alloc_of_wager
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:55:01.216606+00:00
-- url     : https://prove2.me/submissions/c9f2feb1-1cd7-4f98-8844-a513fa4aedac

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

open WagerFairDiv in
theorem solution {n m : ℕ} (A B : Mech n m) (hAB : Corresponding A B) :
    (WagerWeakIC B → AllocWeakIC A) ∧ (WagerStrictIC B → AllocStrictIC A) := by
  have hB : ∀ p w i, B p w i = fun j => w.total * A p w i j := fun p w i => funext (hAB p w i)
  have hval : ∀ (x : Fin m → ℝ) (c : ℝ) (y : Fin m → ℝ),
      WagerFairDiv.val x (fun j => c * y j) = c * WagerFairDiv.val x y := by
    intro x c y
    unfold WagerFairDiv.val
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have htot : ∀ (w : PosVec n) (i : Fin n), 0 < w.total := by
    intro w i
    have h1 : w.1 i ≤ ∑ j, w.1 j :=
      Finset.single_le_sum (fun j _ => (w.2 j).le) (Finset.mem_univ i)
    unfold PosVec.total
    linarith [w.2 i]
  have weak : WagerWeakIC B → AllocWeakIC A := by
    intro hW i vi v e
    have h := hW i vi v e
    rw [hB, hB, hval, hval] at h
    exact le_of_mul_le_mul_left h (htot e i)
  refine ⟨weak, fun hS => ⟨weak hS.1, fun i vi v e hne => ?_⟩⟩
  have h := hS.2 i vi v e hne
  rw [hB, hB, hval, hval] at h
  exact lt_of_mul_lt_mul_left h (htot e i).le
