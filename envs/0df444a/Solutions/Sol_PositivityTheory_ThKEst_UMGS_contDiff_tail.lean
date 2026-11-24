-- Prove2me | solution 1 for PositivityTheory.ThKEst.UMGS.contDiff_tail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:06.799806+00:00
-- url     : https://prove2.me/submissions/92989961-591a-4293-882d-922b8e834054

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_UMGSmoothA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.UMGS
open Filter Topology Function
variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKEst.UMGS
theorem _root_.solution (k : ℕ) (n : WithTop ℕ∞) : ContDiff ℝ n fun (t : Fin (k + 1) → ℝ) (i : Fin k) => t i.succ :=
  contDiff_pi.2 fun i => contDiff_apply ℝ ℝ i.succ
end PositivityTheory.ThKEst.UMGS
