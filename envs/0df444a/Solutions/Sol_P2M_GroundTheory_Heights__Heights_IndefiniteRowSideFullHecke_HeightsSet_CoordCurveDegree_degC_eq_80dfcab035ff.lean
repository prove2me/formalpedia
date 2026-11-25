-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_degC_eq_80dfcab035ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:30:18.797912+00:00
-- url     : https://prove2.me/submissions/9e8d3db1-798b-4a95-8bb1-60ba364ef23f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_blockFnField_eq_2808a9951dc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_ptOf_chart_96d5086227b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_ptOf_mem_82cf1c473c61
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_scale_equivalence_54ce06ff168c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_exists_ptOf_2ca38ad1a588
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_X_mem_of_eq_zero_e9e44dbdbf54


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
theorem _root_.solution {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) :
    degC (mCoordIdeal y) = Nat.card (blockFnField y →ₐ[ℚ] ℂ) := by
  choose c hc0 using hP.2.1.2.2
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h ↦ hc0 k (X_mem_of_eq_zero h)
  unfold degC
  refine (Nat.card_eq_of_bijective (fun φ ↦ Quot.mk _ ⟨ptOf y c φ, ptOf_mem hc φ⟩) ⟨fun φ ψ h ↦ ?_,
    fun w ↦ ?_⟩).symm
  · obtain ⟨s, -, hs⟩ :=
      (Equivalence.eqvGen_iff (scale_equivalence (mCoordIdeal y))).mp (Quot.eqvGen_exact h)
    have hs1 : ∀ k, s k = 1 := fun k ↦ by
      have := congrFun hs ⟨k, c k⟩
      simp only [ptOf_chart hc, mul_one] at this
      exact this.symm
    have hpt : ptOf y c ψ = ptOf y c φ := by
      funext p
      have := congrFun hs p
      simp only [hs1, one_mul] at this
      exact this
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (blockFnField_eq y c hc) ?_
    rintro _ ⟨p, rfl⟩
    exact congrFun hpt.symm p
  · obtain ⟨⟨z, hz⟩, rfl⟩ := Quot.exists_rep w
    obtain ⟨φ, hφ, hzc⟩ := exists_ptOf hP hc hz
    exact ⟨φ, (Quot.sound ⟨fun k ↦ (z ⟨k, c k⟩)⁻¹, fun k ↦ inv_ne_zero (hzc k), hφ⟩).symm⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
