-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointArithIntersection_sum_reps_eq_be09dc743a8b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:32:12.128746+00:00
-- url     : https://prove2.me/submissions/d11441dd-d69a-4e2d-8cde-e7e4ab1559ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPointArInt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointArithIntersection_eq_of_ptOf_eq_smul_c4234cca63a4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_exists_ptOf_2ca38ad1a588
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_ptOf_mem_82cf1c473c61


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.PointArithIntersection
open IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
variable {T : Type} [Fintype T]
variable {K' : Type} [Field K'] [NumberField K']
namespace GroundTheory.Heights₂.Heights.PointArithIntersection
theorem _root_.solution {y : (Σ _ : Unit, T) → K'} (hP : IsArithVar (mCoordIdeal y) 1) {c : Unit → T}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (R : Finset ((Σ _ : Unit, T) → ℂ))
    (hR : ∀ t ∈ R, t ∈ mcPts (mCoordIdeal y))
    (hU : ∀ z ∈ mcPts (mCoordIdeal y), ∃! t, t ∈ R ∧ SameOrbit z t)
    (F : ((Σ _ : Unit, T) → ℂ) → ℝ) (hF : ∀ t : ℂ, t ≠ 0 → ∀ z, F (fun p => t * z p) = F z)
    [Fintype (blockFnField y →ₐ[ℚ] ℂ)] :
    ∑ t ∈ R, F t = ∑ φ : blockFnField y →ₐ[ℚ] ℂ, F (ptOf y c φ) := by
  have hex : ∀ t ∈ R, ∃ φ : blockFnField y →ₐ[ℚ] ℂ,
      ptOf y c φ = (fun p => (t ⟨p.1, c p.1⟩)⁻¹ * t p) ∧ ∀ k, t ⟨k, c k⟩ ≠ 0 :=
    fun t ht => exists_ptOf hP hc (hR t ht)
  refine Finset.sum_bij (fun t ht => (hex t ht).choose) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro t ht t' ht' he
    have h1 := (hex t ht).choose_spec
    have h2 := (hex t' ht').choose_spec
    rw [he] at h1
    obtain ⟨u, -, hu⟩ := hU t (hR t ht)
    have e1 : t = u := hu t ⟨ht, ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩⟩
    have e2 : t' = u := by
      refine hu t' ⟨ht', fun k => t ⟨k, c k⟩ * (t' ⟨k, c k⟩)⁻¹,
        fun k => mul_ne_zero (h1.2 k) (inv_ne_zero (h2.2 k)), funext fun p => ?_⟩
      have := congrFun (h1.1.symm.trans h2.1) p
      have h0 := h1.2 p.1
      have h0' := h2.2 p.1
      simp only at this ⊢
      rw [show t p = t ⟨p.1, c p.1⟩ * ((t ⟨p.1, c p.1⟩)⁻¹ * t p) by field_simp, this]
      ring
    rw [e1, e2]
  · intro φ _
    obtain ⟨u, ⟨hu, ⟨d, hd, hdu⟩⟩, -⟩ := hU _ (ptOf_mem hc φ)
    refine ⟨u, hu, eq_of_ptOf_eq_smul hc ((u ⟨(), c ()⟩)⁻¹ * (d ())⁻¹) ?_⟩
    rw [(hex u hu).choose_spec.1, hdu]
    funext p
    have h0 := hd ()
    ring_nf
    field_simp
  · intro t ht
    rw [(hex t ht).choose_spec.1]
    exact (hF _ (inv_ne_zero ((hex t ht).choose_spec.2 ())) t).symm
end GroundTheory.Heights₂.Heights.PointArithIntersection
