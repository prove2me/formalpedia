-- Prove2me | solution 1 for PositivityTheory.ThKH.Locrep.ev_put
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:58.981+00:00
-- url     : https://prove2.me/submissions/da7c4edd-28c0-42e2-a862-bfa4187ee291

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
theorem _root_.solution (h : ∀ y, ev (ι y) = y) (x : A) (y : K) : ev (put ev ι x y) = y := by
  simp [put, h]
end PositivityTheory.ThKH.Locrep
