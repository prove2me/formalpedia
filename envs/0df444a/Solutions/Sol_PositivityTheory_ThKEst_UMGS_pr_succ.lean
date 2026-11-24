-- Prove2me | solution 1 for PositivityTheory.ThKEst.UMGS.pr_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:36.525871+00:00
-- url     : https://prove2.me/submissions/263935bb-4f5a-462b-b44f-af8d718868d0

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
omit [TopologicalSpace G] [ContinuousMul G]
namespace PositivityTheory.ThKEst.UMGS
theorem _root_.solution {k : ℕ} (γ : Fin (k + 1) → (Multiplicative ℝ →* G)) (t : Fin (k + 1) → ℝ) :
    pr γ t = γ 0 (Multiplicative.ofAdd (t 0)) * pr (fun i => γ i.succ) (fun i => t i.succ) := by
  simp [pr, List.ofFn_succ]
end PositivityTheory.ThKEst.UMGS
