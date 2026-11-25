-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_eval_eq_080797a46129
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:28.163404+00:00
-- url     : https://prove2.me/submissions/5dbc8931-433a-4f8f-88c6-c2e4b7d9d688

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualCurvePoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_combo_326d57212312

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
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} [Fintype T]
  [DecidableEq T]
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.DualCurvePointAlt
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice F)) (t0 : T) (w : Fin i → K) :
    ∃ g : MvPolynomial (Σ _ : Unit, T) ℚ,
      eval₂ (Rat.castHom _) (fun p => dualLatticeCoord b p / dualLatticeCoord b ⟨(), t0⟩) g =
        linVal w / dualLatticeCoord b ⟨(), t0⟩ := by
  obtain ⟨D, c, hD, h⟩ := exists_combo b w
  refine ⟨∑ t, C ((c t : ℚ) / D) * X ⟨(), t⟩, ?_⟩
  have hD' : (D : ProjField K i) ≠ 0 := Int.cast_ne_zero.mpr hD
  have hl : linVal w = ∑ t, ((c t : ProjField K i) / D) * dualLatticeCoord b ⟨(), t⟩ := by
    rw [← mul_div_cancel_left₀ (linVal w) hD', h, Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hl, Finset.sum_div, eval₂_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [eval₂_mul, eval₂_C, eval₂_X, map_div₀, map_intCast, map_intCast]
  ring
end GroundTheory.Heights₂.Heights.DualCurvePointAlt
