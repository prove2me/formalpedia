-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingBitCrossSelectedSupportEmbedding_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/1687b7ae-a7c2-4ef3-b9dd-9a3d4eedc7dd

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_left_external_eval
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_external_right_eval
import Theorems.Thm_PermanentFormulaLowerBound_matchingBitCrossSelected_full_cols_spec

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {ell m : ℕ} (p q : Fin m → ℂ)
    {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab)
    (t : ↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
        (matchingPermutationOutsideFactor
          (matchingDiagonalEmbedding ell m) σ.1.1
          (matchingBitCrossSelectedSupportEmbedding σ t)) =
      match t with
      | .inl u =>
          p ((matchingCrossRows
            (matchingBitCrossSelectedToCross σ) (.inl u)).1) ^
              (2 ^ (u.1 : ℕ))
      | .inr v =>
          q ((matchingCrossCols
            (matchingBitCrossSelectedToCross σ) (.inr v)).1) ^
              (2 ^ (v.1 : ℕ)) := by
  cases t with
  | inl u =>
      have hrow := matchingBitCrossSelected_full_rows_spec σ (.inl u)
      change
        σ.1.1 (matchingBlockIndexEquiv ell m (.inl (.inl u.1))) =
          matchingBlockIndexEquiv ell m
            (.inr (matchingCrossRows
              (matchingBitCrossSelectedToCross σ) (.inl u)).1)
        at hrow
      exact matchingPermutationOutsideFactor_left_external_eval
        p q σ.1.1 u.1
        (matchingCrossRows
          (matchingBitCrossSelectedToCross σ) (.inl u)).1 hrow
  | inr v =>
      have hcol := matchingBitCrossSelected_full_cols_spec σ (.inr v)
      change
        σ.1.1 (matchingBlockIndexEquiv ell m
          (.inr (matchingCrossCols
            (matchingBitCrossSelectedToCross σ) (.inr v)).1)) =
          matchingBlockIndexEquiv ell m (.inl (.inr v.1))
        at hcol
      have hpre :
          σ.1.1.symm
            (matchingBlockIndexEquiv ell m (.inl (.inr v.1))) =
              matchingBlockIndexEquiv ell m
                (.inr (matchingCrossCols
                  (matchingBitCrossSelectedToCross σ) (.inr v)).1) :=
        σ.1.1.symm_apply_eq.mpr hcol.symm
      change
        MvPolynomial.eval (matchingPermanentSpecialization p q)
          (matchingPermutationOutsideFactor
            (matchingDiagonalEmbedding ell m) σ.1.1
            (σ.1.1.symm
              (matchingBlockIndexEquiv ell m (.inl (.inr v.1))))) = _
      rw [hpre]
      exact matchingPermutationOutsideFactor_external_right_eval
        p q σ.1.1
        (matchingCrossCols
          (matchingBitCrossSelectedToCross σ) (.inr v)).1 v.1 hcol
end PermanentFormulaLowerBound
