-- Prove2me | solution 1 for ThreeSum.TernaryBank.deficit_generating_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:03:51.892939+00:00
-- url     : https://prove2.me/submissions/399e5e6e-3f98-4302-8c56-947407a1f1fc

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryBank_digit_deficit_sum
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType
namespace ThreeSum.TernaryBank
theorem _root_.solution {N : ℕ} (Q : TritWord N) (z : ℝ) :
    (∑ R ∈ lowerWords Q, z ^ deficit Q R) =
      ∏ i : Fin N, (if Q i = 0 then 1 else if Q i = 1 then 1 + z
        else 1 + z + z ^ 2) := by
  have hpoint (R : TritWord N) :
      (∏ i, digitDeficitWeight z (Q i) (R i)) =
        if Below R Q then z ^ deficit Q R else 0 := by
    by_cases h : Below R Q
    · simp only [h, ↓reduceIte]
      have heq : (∏ i : Fin N, digitDeficitWeight z (Q i) (R i)) =
          ∏ i : Fin N, z ^ ((Q i).val - (R i).val) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [digitDeficitWeight, h i]
      rw [heq]
      exact Finset.prod_pow_eq_pow_sum (univ : Finset (Fin N)) _ _
    · simp only [h, ↓reduceIte]
      obtain ⟨i, hi⟩ := not_forall.mp h
      apply Finset.prod_eq_zero (mem_univ i)
      simp [digitDeficitWeight, hi]
  calc
    (∑ R ∈ lowerWords Q, z ^ deficit Q R) =
        ∑ R : TritWord N, if Below R Q then z ^ deficit Q R else 0 := by
      simp [lowerWords, Finset.sum_filter]
    _ = ∑ R : TritWord N, ∏ i, digitDeficitWeight z (Q i) (R i) := by
      apply Finset.sum_congr rfl
      intro R hR
      exact (hpoint R).symm
    _ = ∏ i : Fin N, ∑ r : Fin 3, digitDeficitWeight z (Q i) r :=
      (Fintype.prod_sum _).symm
    _ = _ := by simp only [digit_deficit_sum]
end ThreeSum.TernaryBank
