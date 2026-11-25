-- Prove2me | solution 1 for PositivityTheory.ThKH.Locrep.put_put
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:01:53.460747+00:00
-- url     : https://prove2.me/submissions/db60d609-e82d-439b-a6d1-d07ec876dab7

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
variable {ev ι}
namespace PositivityTheory.ThKH.Locrep
theorem _root_.solution (h : ∀ y, ev (ι y) = y) (x : A) (y z : K) : put ev ι (put ev ι x y) z = put ev ι x z := by
  simp only [put, map_add, map_sub, h, sub_self, zero_add]
  abel
end PositivityTheory.ThKH.Locrep
