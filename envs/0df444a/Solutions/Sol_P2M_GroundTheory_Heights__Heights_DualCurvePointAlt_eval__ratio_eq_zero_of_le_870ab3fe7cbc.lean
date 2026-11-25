-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_eval__ratio_eq_zero_of_le_870ab3fe7cbc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:48:54.027813+00:00
-- url     : https://prove2.me/submissions/f87d7f30-d40c-423f-9daf-bbca91219d7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualCurvePoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_aeval_ratio_eq_zero_of_le_3480b1786d6e

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
namespace GroundTheory.Heights₂.Heights.DualCurvePointAlt
theorem _root_.solution {Ω L : Type} [Field Ω] [CharZero Ω] [Field L] [CharZero L]
    {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → L} (hyz : mCoordIdeal y ≤ mCoordIdeal z) (d : ∀ k, ι k)
    (hyd : ∀ k, y ⟨k, d k⟩ ≠ 0) (hzd : ∀ k, z ⟨k, d k⟩ ≠ 0) {g : MvPolynomial (Σ k, ι k) ℚ}
    (hg0 : eval₂ (Rat.castHom Ω) (fun p => y p / y ⟨p.1, d p.1⟩) g = 0) :
    eval₂ (Rat.castHom L) (fun p => z p / z ⟨p.1, d p.1⟩) g = 0 := by
  have := aeval_ratio_eq_zero_of_le hyz d hyd hzd (g := g) (by rw [aeval_def]; exact hg0)
  rwa [aeval_def] at this
end GroundTheory.Heights₂.Heights.DualCurvePointAlt
