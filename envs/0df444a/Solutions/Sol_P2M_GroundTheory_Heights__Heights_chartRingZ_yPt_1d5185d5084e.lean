-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chartRingZ_yPt_1d5185d5084e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:37.741984+00:00
-- url     : https://prove2.me/submissions/2efc23db-efad-4958-b31b-82177806b62a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps

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
theorem _root_.solution (c : ∀ _ : Unit, PBlk 1 ()) :
    chartRingZ IndefiniteRowSideFullHecke.HeightsSet.yPt c = ⊥ := by
  refine eq_bot_iff.mpr (Algebra.adjoin_le ?_)
  rintro _ ⟨p, rfl⟩
  simp [IndefiniteRowSideFullHecke.HeightsSet.yPt]
end GroundTheory.Heights₂.Heights
