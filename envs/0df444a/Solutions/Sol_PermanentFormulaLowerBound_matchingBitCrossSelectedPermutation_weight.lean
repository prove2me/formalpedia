-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingBitCrossSelectedPermutation_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/81d91705-7e23-43f6-9b79-f15564d82c45

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_external_external_eval
import Theorems.Thm_PermanentFormulaLowerBound_matchingBitCrossSelected_factor_one_off_support
import Theorems.Thm_PermanentFormulaLowerBound_matchingBitCrossSelectedSupportEmbedding_factor

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
    (σ : MatchingBitCrossSelectedPermutation ell m de ab) :
    (∏ i : {i : Fin ((ell + ell) + m) //
        i ≠ (matchingExternalEntry ell m ab.1 ab.2).1.1},
      MvPolynomial.eval (matchingPermanentSpecialization p q)
        (matchingPermutationOutsideFactor
          (matchingDiagonalEmbedding ell m) σ.1.1 i.1)) =
      matchingCrossWeight p q
        (matchingBitSubset ell (de.1 : ℕ))
        (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2
        (matchingBitCrossSelectedToCross σ) := by
  classical
  let f : Fin ((ell + ell) + m) → ℂ := fun i =>
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor
        (matchingDiagonalEmbedding ell m) σ.1.1 i)
  have hrest (i : Fin ((ell + ell) + m))
      (hi : i ∉ Set.range (matchingBitCrossSelectedSupportEmbedding σ)) :
      f i = 1 := by
    apply matchingBitCrossSelected_factor_one_off_support
      p q de ab σ i
    · intro u hu
      exact hi ⟨.inl u, hu.symm⟩
    · intro v hv
      exact hi ⟨.inr v, hv.symm⟩
  have hfull :
      (∏ i : Fin ((ell + ell) + m), f i) =
        matchingCrossWeight p q
          (matchingBitSubset ell (de.1 : ℕ))
          (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2
          (matchingBitCrossSelectedToCross σ) := by
    calc
      (∏ i : Fin ((ell + ell) + m), f i) =
          ∏ t : ↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
            ↥(matchingBitSubset ell (de.2 : ℕ)),
              f (matchingBitCrossSelectedSupportEmbedding σ t) := by
        symm
        exact Fintype.prod_of_injective
          (matchingBitCrossSelectedSupportEmbedding σ)
          (matchingBitCrossSelectedSupportEmbedding σ).injective
          (fun t => f (matchingBitCrossSelectedSupportEmbedding σ t))
          f hrest (fun _ => rfl)
      _ =
          ∏ t : ↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
            ↥(matchingBitSubset ell (de.2 : ℕ)),
              match t with
              | .inl u =>
                  p ((matchingCrossRows
                    (matchingBitCrossSelectedToCross σ) (.inl u)).1) ^
                      (2 ^ (u.1 : ℕ))
              | .inr v =>
                  q ((matchingCrossCols
                    (matchingBitCrossSelectedToCross σ) (.inr v)).1) ^
                      (2 ^ (v.1 : ℕ)) := by
        apply Finset.prod_congr rfl
        intro t _
        exact matchingBitCrossSelectedSupportEmbedding_factor p q σ t
      _ = matchingCrossWeight p q
          (matchingBitSubset ell (de.1 : ℕ))
          (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2
          (matchingBitCrossSelectedToCross σ) := by
        rw [Fintype.prod_sum_type]
        rfl
  have hderiv :
      f (matchingExternalEntry ell m ab.1 ab.2).1.1 = 1 := by
    exact matchingPermutationOutsideFactor_external_external_eval
      p q σ.1.1 ab.1 ab.2
      (matchingBitSelectedPermutation_external σ.1)
  have hdeleted := Fintype.prod_eq_mul_prod_subtype_ne f
    (matchingExternalEntry ell m ab.1 ab.2).1.1
  rw [hderiv, one_mul] at hdeleted
  exact hdeleted.symm.trans hfull
end PermanentFormulaLowerBound
