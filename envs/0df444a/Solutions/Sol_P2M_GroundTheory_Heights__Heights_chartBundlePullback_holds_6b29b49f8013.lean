-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chartBundlePullback_holds_6b29b49f8013
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:58.594602+00:00
-- url     : https://prove2.me/submissions/b39e1135-f453-4355-b52d-18fd097879b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AlgebraMapMemChartRingJoinPt

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo TensorProduct
variable {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type}
variable {E : Type} [AddCommGroup E] [Module Ω E]
variable {r : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : ChartBundlePullback.Statement :=
  fun _ _ _ _ _ _ _ _ _ _ z _ _ _ _ B => ⟨pullbackBundle B z, fun _ => rfl⟩
end GroundTheory.Heights₂.Heights
