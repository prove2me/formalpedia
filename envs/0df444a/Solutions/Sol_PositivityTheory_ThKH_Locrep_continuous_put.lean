-- Prove2me | solution 1 for PositivityTheory.ThKH.Locrep.continuous_put
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:23:50.656981+00:00
-- url     : https://prove2.me/submissions/82d9ce71-78ca-446b-a2d5-855da1b999a9

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
variable [TopologicalSpace A] [IsTopologicalAddGroup A] [TopologicalSpace K] [IsTopologicalAddGroup K]
omit [IsTopologicalAddGroup K]
namespace PositivityTheory.ThKH.Locrep
theorem _root_.solution (hev : Continuous ev) (hι : Continuous ι) : Continuous fun p : A × K => put ev ι p.1 p.2 := by
  show Continuous fun p : A × K => p.1 - ι (ev p.1) + ι p.2
  exact (continuous_fst.sub (hι.comp (hev.comp continuous_fst))).add (hι.comp continuous_snd)
end PositivityTheory.ThKH.Locrep
