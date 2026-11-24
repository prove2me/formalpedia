-- Prove2me | solution 1 for P2M_CompanionTheory_ThKR_Mp_MpE_toBlocks___one__0a88a243d007
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:23:53.084184+00:00
-- url     : https://prove2.me/submissions/3af84545-f1a0-4197-9565-b4b35f28a362

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticGroupT2Space

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open CompanionTheory.ThKR.Mp.MpE
omit [Fintype l]
namespace CompanionTheory.ThKR.Mp.MpE
theorem _root_.solution : (1 : Mat l).toBlocks₁₁ = 1 := by
  ext a b
  simp [Matrix.toBlocks₁₁, Matrix.one_apply]
end CompanionTheory.ThKR.Mp.MpE
