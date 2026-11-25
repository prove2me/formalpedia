-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_exists_ptOf_2ca38ad1a588
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:23:12.293551+00:00
-- url     : https://prove2.me/submissions/c11e40ec-6b31-450f-b700-9c9e53e1e537

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_blockFnField_eq_2808a9951dc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_ptOf_chart_96d5086227b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_aeval_pt_eq_zero_33c7e75b522c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_X_mem_of_eq_zero_e9e44dbdbf54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_isAlgebraic_blockFnField_1c5e3fe2724f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
theorem _root_.solution {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) {c : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∃ φ : blockFnField y →ₐ[ℚ] ℂ, ptOf y c φ = (fun p ↦ (z ⟨p.1, c p.1⟩)⁻¹ * z p) ∧
      ∀ k, z ⟨k, c k⟩ ≠ 0 := by
  have halg := isAlgebraic_blockFnField hP
  choose d hd using hz.1
  have hyd : ∀ k, y ⟨k, d k⟩ ≠ 0 := fun k h ↦ hd k (by simpa using hz.2 _ (X_mem_of_eq_zero h))
  let ev : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] blockFnField y := aeval (ratioF y d)
  have hval : ∀ g, ((ev g : blockFnField y) : Ω) = aeval (fun p ↦ y p / y ⟨p.1, d p.1⟩) g :=
    fun g ↦ comp_aeval_apply (f := ratioF y d) (blockFnField y).val g
  have hsurj : Function.Surjective ev := by
    intro x
    have hx : (x : Ω) ∈ Algebra.adjoin ℚ (Set.range fun p ↦ y p / y ⟨p.1, d p.1⟩) := by
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic, ← blockFnField_eq y d hyd]
      · exact x.2
      · rintro _ ⟨p, rfl⟩
        exact IntermediateField.isAlgebraic_iff.mp (halg.isAlgebraic (ratioF y d p))
    rw [Algebra.adjoin_range_eq_range_aeval] at hx
    obtain ⟨g, hg⟩ := hx
    exact ⟨g, Subtype.ext ((hval g).trans hg)⟩
  have hker : ∀ g ∈ RingHom.ker ev, aeval (fun p ↦ z p / z ⟨p.1, d p.1⟩) g = 0 := fun g hg ↦
    aeval_pt_eq_zero hP d hyd hz hd (by rw [← hval, RingHom.mem_ker.mp hg]; rfl)
  let φ : blockFnField y →ₐ[ℚ] ℂ :=
    (Ideal.Quotient.liftₐ (RingHom.ker ev) (aeval fun p ↦ z p / z ⟨p.1, d p.1⟩) hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom
  have hφ : ∀ g, φ (ev g) = aeval (fun p ↦ z p / z ⟨p.1, d p.1⟩) g := fun g ↦ by
    have : (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (ev g) = Ideal.Quotient.mk _ g := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change (Ideal.Quotient.liftₐ (RingHom.ker ev) _ hker)
      ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (ev g)) = _
    rw [this]
    rfl
  have hpt : ∀ p, ptOf y c φ p = z p / z ⟨p.1, c p.1⟩ := fun p ↦ by
    have e : ratioF y c p = ev (X p) / ev (X ⟨p.1, c p.1⟩) := by
      apply Subtype.ext
      simp only [ev, aeval_X, ratioF, IntermediateField.coe_div]
      exact (div_div_div_cancel_right₀ (hyd p.1) _ _).symm
    rw [ptOf, e, map_div₀, hφ, hφ, aeval_X, aeval_X]
    exact div_div_div_cancel_right₀ (hd p.1) _ _
  have hzc : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h ↦ by
    have := ptOf_chart hc φ k
    rw [hpt, h, div_zero] at this
    exact zero_ne_one this
  exact ⟨φ, funext fun p ↦ by rw [hpt, div_eq_inv_mul], hzc⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
