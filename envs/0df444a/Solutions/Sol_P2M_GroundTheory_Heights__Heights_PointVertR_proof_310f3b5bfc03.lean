-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointVertR_proof_310f3b5bfc03
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:16:26.447178+00:00
-- url     : https://prove2.me/submissions/355789e7-8c41-439a-a54b-c378091af9c4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPointVertR
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointVertRAux_degC_eq_finrank_02d1f9d69ae7

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace PointVertR
theorem _root_.solution (hI : VertRIndex.Statement) (hN : SectionIndexNorm.Statement) :
    PointVertR.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  rw [hI T K' y s hP hs hsP, PointVertRAux.degC_eq_finrank hP,
    ← Module.finrank_mul_finrank ℚ (blockFnField y) K', Nat.cast_mul, mul_assoc,
    hN T K' y s hP hs hsP]
end PointVertR
end GroundTheory.Heights₂.Heights
