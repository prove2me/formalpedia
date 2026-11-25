-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_ratio_eq_zero_of_le_3480b1786d6e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:30:37.299743+00:00
-- url     : https://prove2.me/submissions/ae9d8f90-dbbe-4975-ae0b-a0b5c0b44fd2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualCurvePoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_eq_zero_of_mem_3ac1f31f332f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_ker_coneMapQ_eq_b779a2ea9f5e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_blockDeg_le_totalDegree_f38221eff11e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_eval__homog_d7bc17bd6f0e


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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualCurvePointAlt
variable {B : Type} [Fintype B] {ι : B → Type} [∀ k, Fintype (ι k)]
set_option linter.unusedSectionVars false
open IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
namespace GroundTheory.Heights₂.Heights.DualCurvePointAlt
theorem _root_.solution {Ω L : Type} [Field Ω] [CharZero Ω] [Field L] [CharZero L]
    {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → L} (hyz : mCoordIdeal y ≤ mCoordIdeal z) (d : ∀ k, ι k)
    (hyd : ∀ k, y ⟨k, d k⟩ ≠ 0) (hzd : ∀ k, z ⟨k, d k⟩ ≠ 0) {g : MvPolynomial (Σ k, ι k) ℚ}
    (hg0 : aeval (fun p => y p / y ⟨p.1, d p.1⟩) g = 0) :
    aeval (fun p => z p / z ⟨p.1, d p.1⟩) g = 0 := by
  have hN : ∀ m ∈ g.support, ∀ k, blockDeg m k ≤ g.totalDegree := fun m hm k =>
    blockDeg_le_totalDegree hm k
  have hG : homog d g.totalDegree g ∈ RingHom.ker (coneMapQ y) := by
    rw [RingHom.mem_ker]
    let j := algebraMap (MvPolynomial B Ω) (FractionRing (MvPolynomial B Ω))
    have hj : Function.Injective j := IsFractionRing.injective _ _
    apply hj
    have hw : ∀ k, (j ∘ fun p : Σ k, ι k => C (y p) * X p.1) ⟨k, d k⟩ ≠ 0 := fun k =>
      (map_ne_zero_iff j hj).mpr (mul_ne_zero (C_ne_zero.mpr (hyd k)) (X_ne_zero _))
    rw [map_zero, coneMapQ, aeval_def, eval₂_comp_left, eval₂_homog _ d _ g hN _ hw]
    apply mul_eq_zero_of_right
    have e : (fun p : Σ k, ι k => (j ∘ fun p : Σ k, ι k => C (y p) * X p.1) p /
        (j ∘ fun p : Σ k, ι k => C (y p) * X p.1) ⟨p.1, d p.1⟩) =
        (j.comp C) ∘ fun p => y p / y ⟨p.1, d p.1⟩ := by
      funext p
      have hX : j (X p.1) ≠ 0 := (map_ne_zero_iff j hj).mpr (X_ne_zero _)
      simp only [Function.comp_apply, map_mul, RingHom.coe_comp]
      rw [mul_div_mul_right _ _ hX, ← RingHom.comp_apply, ← RingHom.comp_apply, ← RingHom.comp_apply,
        map_div₀]
    rw [e, show j.comp (algebraMap ℚ (MvPolynomial B Ω)) = (j.comp C).comp (algebraMap ℚ Ω) from
      RingHom.ext_rat _ _, ← eval₂_comp_left, ← aeval_def, hg0, map_zero]
  have hGz : aeval z (homog d g.totalDegree g) = 0 := by
    rw [ker_coneMapQ_eq y] at hG
    have hle : ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) ≤
        RingHom.ker (aeval z : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] L) := by
      refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq, aeval_map_algebraMap, aeval_def,
        algebraMap_int_eq]
      exact aeval_eq_zero_of_mem (hyz hf)
    exact hle hG
  rw [aeval_def, eval₂_homog _ d _ g hN _ hzd] at hGz
  rw [aeval_def]
  exact (mul_eq_zero.mp hGz).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hzd k))
end GroundTheory.Heights₂.Heights.DualCurvePointAlt
