-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPermanentJacobian_eq_weighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/7d0251db-e911-4d10-b2e1-591bfb454f58

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingWeightedCrossBitPermutation_sum
import Theorems.Thm_PermanentFormulaLowerBound_matchingBitCrossSelectedPermutation_weight
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermanentJacobian_eq_cross_selected_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {ell m : ℕ} (p q : Fin m → ℂ) :
    matchingPermanentJacobian (ell := ell) p q =
      matchingWeightedBivariateEvaluationMatrix p q
        (fun d : Fin m => matchingBitSubset ell (d : ℕ))
        (fun e : Fin m => matchingBitSubset ell (e : ℕ)) := by
  classical
  ext de ab
  calc
    matchingPermanentJacobian (ell := ell) p q de ab =
      ∑ σ : MatchingBitCrossSelectedPermutation ell m de ab,
        ∏ i : {i : Fin ((ell + ell) + m) //
          i ≠ (matchingExternalEntry ell m ab.1 ab.2).1.1},
          MvPolynomial.eval (matchingPermanentSpecialization p q)
            (matchingPermutationOutsideFactor
              (matchingDiagonalEmbedding ell m) σ.1.1 i.1) :=
      matchingPermanentJacobian_eq_cross_selected_sum p q de ab
    _ =
      ∑ σ : MatchingBitCrossSelectedPermutation ell m de ab,
        matchingCrossWeight p q
          (matchingBitSubset ell (de.1 : ℕ))
          (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2
          (matchingBitCrossSelectedToCross σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      exact matchingBitCrossSelectedPermutation_weight
        p q de ab σ
    _ =
      ∑ τ : MatchingCrossPermutation
        (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
          ↥(matchingBitSubset ell (de.2 : ℕ)))
        {j : Fin m // j ≠ ab.1}
        {j : Fin m // j ≠ ab.2},
        matchingCrossWeight p q
          (matchingBitSubset ell (de.1 : ℕ))
          (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2 τ := by
      apply Fintype.sum_equiv
        (matchingBitCrossSelectedEquiv ell m de ab)
      intro σ
      rfl
    _ = matchingWeightedBivariateEvaluationMatrix p q
        (fun d : Fin m => matchingBitSubset ell (d : ℕ))
        (fun e : Fin m => matchingBitSubset ell (e : ℕ)) de ab :=
      matchingWeightedCrossBitPermutation_sum p q de ab
end PermanentFormulaLowerBound
