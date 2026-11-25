-- Prove2me | solution 1 for PositivityTheory.ThKH.Locrep.put_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:01:55.125665+00:00
-- url     : https://prove2.me/submissions/68d6b27a-0994-4bdc-8049-2a26e75b83ae

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_LocrepSB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Locrep
open Filter Topology GlobalTheory.WeilM
variable {A K : Type} [AddCommGroup A] [AddCommGroup K] (ev : A →+ K) (ι : K →+ A)
namespace PositivityTheory.ThKH.Locrep
theorem _root_.solution (x : A) : put ev ι x (ev x) = x := by
  simp [put]
end PositivityTheory.ThKH.Locrep
