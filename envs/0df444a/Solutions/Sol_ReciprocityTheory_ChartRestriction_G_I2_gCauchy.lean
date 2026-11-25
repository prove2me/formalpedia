-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.gCauchy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:51.736747+00:00
-- url     : https://prove2.me/submissions/2cf5cbac-ab8c-4d94-87ce-17532400f9da

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchy
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cauchy_gauss_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_contDiff_of_differentiable_fd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution : GCauchyStatement := by
  intro ι _ F hF S hS α
  set N := Fintype.card ι
  let e : ι ≃ Fin N := Fintype.equivFin ι

  let T : (Fin N → ℂ) →L[ℂ] EuclideanSpace ℂ ι :=
    (EuclideanSpace.equiv ι ℂ).symm.toContinuousLinearMap.comp
      (LinearMap.funLeft ℂ ℂ e).toContinuousLinearMap
  have hT : ∀ z : Fin N → ℂ, ‖T z‖ ^ 2 = ∑ j, ‖z j‖ ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq]
    simp only [T, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
      LinearMap.coe_toContinuousLinearMap', Function.comp_apply, LinearMap.funLeft_apply]
    simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply]
    exact Fintype.sum_equiv e _ _ (fun i => by simp)
  have hTs : ∀ i : ι, T (Pi.single (e i) 1) = EuclideanSpace.single i 1 := by
    intro i
    ext j
    simp only [T, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
      LinearMap.coe_toContinuousLinearMap', Function.comp_apply, LinearMap.funLeft_apply,
      EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, EuclideanSpace.single_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Pi.single_apply, e.injective.ne h]
  set G : (Fin N → ℂ) → ℂ := F ∘ T
  have hG : Differentiable ℂ G := hF.comp T.differentiable
  have hGS : ∀ z, ‖G z‖ ^ 2 * Real.exp (-Real.pi * ∑ i, ‖z i‖ ^ 2) ≤ S := by
    intro z
    have := hS (T z)
    rwa [hT z] at this
  set k := Multiset.card (Finsupp.toMultiset α)
  set l : Fin k → Fin N := fun j =>
    e ((Finsupp.toMultiset α).toList.get (j.cast (Multiset.length_toList _).symm))
  have hc := cauchy_gauss_le G hG S hGS l
  have hF' : ContDiff ℂ k F := contDiff_of_differentiable_fd hF k
  have hcomp : iteratedFDeriv ℂ k G 0 (fun j => Pi.single (l j) 1) =
      iteratedFDeriv ℂ k F 0 (fun j => EuclideanSpace.single
        ((Finsupp.toMultiset α).toList.get (j.cast (Multiset.length_toList _).symm)) 1) := by
    rw [show G = F ∘ T from rfl, T.iteratedFDeriv_comp_right hF' 0 le_rfl]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
    congr 1
    funext j
    exact hTs _
  have hk : k = α.degree := by
    simp only [k, Finsupp.card_toMultiset]
    first
      | rfl
      | simp [Finsupp.sum, Finsupp.degree]
  have hdeg : (k : ℝ) = (α.degree : ℝ) := by rw [hk]
  unfold polyDeriv
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl, one_mul]
  rw [← hdeg, ← hcomp]
  exact hc
end ReciprocityTheory.ChartRestriction.G.I2
