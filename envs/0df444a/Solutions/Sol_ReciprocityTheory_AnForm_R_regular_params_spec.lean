-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.regular_params_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:48.448492+00:00
-- url     : https://prove2.me/submissions/bad8540e-38cf-40de-90da-f1b785db8fd7

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RegDom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open IsLocalRing
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R) :
    (∀ i, f i ∉ maximalIdeal R ^ 2) ∧ ∀ i j, i ≠ j → ¬ Associated (f i) (f j) := by
  classical

  have key : Submodule.spanFinrank (maximalIdeal R) = n := by
    have h : (Submodule.spanFinrank (maximalIdeal R) : WithBot ℕ∞) = ringKrullDim R := by
      obtain ⟨h⟩ := ‹IsRegularLocalRing R›
      exact h
    rw [← hdim] at h
    exact_mod_cast h

  have main : ∀ j, f j ∈ Ideal.span (↑((Finset.univ.erase j).image f) : Set R) ⊔
      maximalIdeal R ^ 2 → False := by
    intro j hj
    generalize hS : Ideal.span (↑((Finset.univ.erase j).image f) : Set R) = S at hj
    have hle : maximalIdeal R ≤ S ⊔ maximalIdeal R • maximalIdeal R := by
      rw [← hspan]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      by_cases hk : k = j
      · rw [hk, hspan, Ideal.smul_eq_mul, ← sq]
        exact hj
      · apply Submodule.mem_sup_left
        rw [← hS]
        exact Ideal.subset_span (Finset.mem_coe.mpr
          (Finset.mem_image_of_mem f (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)))
    have hFG : (maximalIdeal R).FG := IsNoetherian.noetherian _
    have hJ : maximalIdeal R ≤ Ideal.jacobson ⊥ :=
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    have hmS : maximalIdeal R ≤ S := Submodule.le_of_le_smul_of_le_jacobson_bot hFG hJ hle
    have hSm : S ≤ maximalIdeal R := by
      rw [← hS, Ideal.span_le]
      intro y hy
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      rw [← hspan]
      exact Ideal.subset_span ⟨a, rfl⟩
    have heq : maximalIdeal R = S := le_antisymm hmS hSm
    have hcard : Submodule.spanFinrank (maximalIdeal R) ≤ n - 1 := by
      rw [heq, ← hS]
      calc Submodule.spanFinrank (Ideal.span (↑((Finset.univ.erase j).image f) : Set R))
          ≤ (↑((Finset.univ.erase j).image f) : Set R).ncard :=
            Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)
        _ = ((Finset.univ.erase j).image f).card := Set.ncard_coe_finset _
        _ ≤ (Finset.univ.erase j).card := Finset.card_image_le
        _ = n - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
    have hn : 0 < n := Fin.pos j
    omega
  refine ⟨fun i hi => main i (Submodule.mem_sup_right hi), fun i j hij hassoc => ?_⟩
  obtain ⟨u, hu⟩ := hassoc
  apply main j
  apply Submodule.mem_sup_left
  rw [← hu]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Finset.mem_coe.mpr
    (Finset.mem_image_of_mem f (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩))))
end ReciprocityTheory.AnForm.R
