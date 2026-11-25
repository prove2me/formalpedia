-- Prove2me | solution 1 for PositivityTheory.ThKEst.UMGS.contDiff_exp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:26.710679+00:00
-- url     : https://prove2.me/submissions/0c04007b-438e-4008-bb74-1cf81ddb4d25

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
theorem _root_.solution (Y : A) (n : WithTop ℕ∞) : ContDiff ℝ n fun t : ℝ => NormedSpace.exp (t • Y) := by
  have h : ContDiff ℝ n (NormedSpace.exp : A → A) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact h.comp (contDiff_id.smul contDiff_const)
end PositivityTheory.ThKEst.UMGS
