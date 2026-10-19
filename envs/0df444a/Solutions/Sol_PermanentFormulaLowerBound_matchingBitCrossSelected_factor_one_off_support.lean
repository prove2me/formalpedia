-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingBitCrossSelected_factor_one_off_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/279336b4-623d-4687-b9b4-5ab76f56f623

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_fixed_diagonal_eval
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_right_external_eval
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_external_left_eval
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_external_external_eval

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {ell m : ℕ} (p q : Fin m → ℂ)
    (de ab : Fin m × Fin m)
    (σ : MatchingBitCrossSelectedPermutation ell m de ab)
    (i : Fin ((ell + ell) + m))
    (hP : ∀ u : ↥(matchingBitSubset ell (de.1 : ℕ)),
      i ≠ matchingBlockIndexEquiv ell m (.inl (.inl u.1)))
    (hQ : ∀ v : ↥(matchingBitSubset ell (de.2 : ℕ)),
      i ≠ σ.1.1.symm
        (matchingBlockIndexEquiv ell m (.inl (.inr v.1)))) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor (matchingDiagonalEmbedding ell m)
        σ.1.1 i) = 1 := by
  classical
  cases hi : (matchingBlockIndexEquiv ell m).symm i with
  | inl y =>
      have hi' : i = matchingBlockIndexEquiv ell m (.inl y) := by
        have h := congrArg (matchingBlockIndexEquiv ell m) hi
        simpa only [Equiv.apply_symm_apply] using h
      subst i
      cases y with
      | inl u =>
          by_cases hu : u ∈ matchingBitSubset ell (de.1 : ℕ)
          · exact False.elim (hP ⟨u, hu⟩ rfl)
          · have hmem :
                Sum.inl u ∈ matchingBitCoefficientSet ell m de :=
              (matchingBitCoefficientSet_mem_inl ell m de u).2 hu
            exact matchingPermutationOutsideFactor_fixed_diagonal_eval
              p q σ.1.1 (.inl u)
              (matchingBitSelectedPermutation_fixed σ.1 (.inl u) hmem)
      | inr v =>
          by_cases hv : v ∈ matchingBitSubset ell (de.2 : ℕ)
          · have hsurv :
                Sum.inr v ∉ matchingBitCoefficientSet ell m de := by
              simpa only [matchingBitCoefficientSet_mem_inr, not_not]
                using hv
            obtain ⟨j, hj⟩ := σ.property ⟨.inr v, hsurv⟩
            exact matchingPermutationOutsideFactor_right_external_eval
              p q σ.1.1 v j hj
          · have hmem :
                Sum.inr v ∈ matchingBitCoefficientSet ell m de :=
              (matchingBitCoefficientSet_mem_inr ell m de v).2 hv
            exact matchingPermutationOutsideFactor_fixed_diagonal_eval
              p q σ.1.1 (.inr v)
              (matchingBitSelectedPermutation_fixed σ.1 (.inr v) hmem)
  | inr a =>
      have hi' : i = matchingBlockIndexEquiv ell m (.inr a) := by
        have h := congrArg (matchingBlockIndexEquiv ell m) hi
        simpa only [Equiv.apply_symm_apply] using h
      subst i
      cases hj : (matchingBlockIndexEquiv ell m).symm
        (σ.1.1 (matchingBlockIndexEquiv ell m (.inr a))) with
      | inl y =>
          have hσ :
              σ.1.1 (matchingBlockIndexEquiv ell m (.inr a)) =
                matchingBlockIndexEquiv ell m (.inl y) := by
            have h := congrArg (matchingBlockIndexEquiv ell m) hj
            simpa only [Equiv.apply_symm_apply] using h
          cases y with
          | inl u =>
              exact matchingPermutationOutsideFactor_external_left_eval
                p q σ.1.1 a u hσ
          | inr v =>
              by_cases hv : v ∈ matchingBitSubset ell (de.2 : ℕ)
              · have hpre := congrArg σ.1.1.symm hσ
                rw [σ.1.1.symm_apply_apply] at hpre
                exact False.elim (hQ ⟨v, hv⟩ hpre)
              · have hmem :
                    Sum.inr v ∈ matchingBitCoefficientSet ell m de :=
                  (matchingBitCoefficientSet_mem_inr ell m de v).2 hv
                have hfixed :=
                  matchingBitSelectedPermutation_fixed
                    σ.1 (.inr v) hmem
                have hsame :
                    σ.1.1 (matchingBlockIndexEquiv ell m (.inr a)) =
                      σ.1.1
                        (matchingBlockIndexEquiv ell m
                          (.inl (.inr v))) :=
                  hσ.trans hfixed.symm
                have hbad :=
                  (matchingBlockIndexEquiv ell m).injective
                    (σ.1.1.injective hsame)
                cases hbad
      | inr b =>
          have hσ :
              σ.1.1 (matchingBlockIndexEquiv ell m (.inr a)) =
                matchingBlockIndexEquiv ell m (.inr b) := by
            have h := congrArg (matchingBlockIndexEquiv ell m) hj
            simpa only [Equiv.apply_symm_apply] using h
          exact matchingPermutationOutsideFactor_external_external_eval
            p q σ.1.1 a b hσ
end PermanentFormulaLowerBound
