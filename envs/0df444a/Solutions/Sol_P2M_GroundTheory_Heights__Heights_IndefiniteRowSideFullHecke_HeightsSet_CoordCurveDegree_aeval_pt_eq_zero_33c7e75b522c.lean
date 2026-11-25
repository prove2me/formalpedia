-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_aeval_pt_eq_zero_33c7e75b522c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:05:20.609821+00:00
-- url     : https://prove2.me/submissions/3462cdda-4378-4ac4-8622-96bf6bcd8054

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_blockDeg_le_totalDegree_f38221eff11e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_eval__homog_d7bc17bd6f0e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_ker_coneMapQ_958512f3981d


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
theorem _root_.solution {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (d : ∀ k, ι k)
    (hyd : ∀ k, y ⟨k, d k⟩ ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (hd : ∀ k, z ⟨k, d k⟩ ≠ 0) {g : MvPolynomial (Σ k, ι k) ℚ}
    (hg0 : aeval (fun p ↦ y p / y ⟨p.1, d p.1⟩) g = 0) :
    aeval (fun p ↦ z p / z ⟨p.1, d p.1⟩) g = 0 := by
  have hN : ∀ m ∈ g.support, ∀ k, blockDeg m k ≤ g.totalDegree := fun m hm k ↦
    blockDeg_le_totalDegree hm k

  have hG : homog d g.totalDegree g ∈ RingHom.ker (coneMapQ y) := by
    rw [RingHom.mem_ker]
    let j := algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω))
    have hj : Function.Injective j := IsFractionRing.injective _ _
    apply hj
    have hw : ∀ k, (j ∘ fun p : Σ k, ι k ↦ C (y p) * X p.1) ⟨k, d k⟩ ≠ 0 := fun k ↦
      (map_ne_zero_iff j hj).mpr (mul_ne_zero (C_ne_zero.mpr (hyd k)) (X_ne_zero _))
    rw [map_zero, coneMapQ, aeval_def, eval₂_comp_left, eval₂_homog _ d _ g hN _ hw]
    apply mul_eq_zero_of_right
    have e : (fun p : Σ k, ι k ↦ (j ∘ fun p : Σ k, ι k ↦ C (y p) * X p.1) p /
        (j ∘ fun p : Σ k, ι k ↦ C (y p) * X p.1) ⟨p.1, d p.1⟩) =
        (j.comp C) ∘ fun p ↦ y p / y ⟨p.1, d p.1⟩ := by
      funext p
      have hX : j (X p.1) ≠ 0 := (map_ne_zero_iff j hj).mpr (X_ne_zero _)
      simp only [Function.comp_apply, map_mul, RingHom.coe_comp]
      rw [mul_div_mul_right _ _ hX, ← RingHom.comp_apply, ← RingHom.comp_apply, ← RingHom.comp_apply,
        map_div₀]
    rw [e, show j.comp (algebraMap ℚ (MvPolynomial K Ω)) = (j.comp C).comp (algebraMap ℚ Ω) from
      RingHom.ext_rat _ _, ← eval₂_comp_left, ← aeval_def, hg0, map_zero]

  have hGz : aeval z (homog d g.totalDegree g) = 0 := by
    rw [ker_coneMapQ hP] at hG
    have hle : ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) ≤
        RingHom.ker (aeval z : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] ℂ) := by
      refine Ideal.map_le_iff_le_comap.mpr fun f hf ↦ ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq, aeval_map_algebraMap, aeval_def]
      have := hz.2 f hf
      rw [eval_map] at this
      convert this using 2
      exact RingHom.ext_int _ _
    exact hle hG
  rw [aeval_def, eval₂_homog _ d _ g hN _ hd] at hGz
  rw [aeval_def]
  exact (mul_eq_zero.mp hGz).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hd k))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
