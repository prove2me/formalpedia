-- Prove2me | solution 1 for PositivityTheory.ThKEst.UMGS.continuous_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:28.595793+00:00
-- url     : https://prove2.me/submissions/b1a2dca0-c7ae-4454-83ff-1943e6133a96

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_UMGSmoothA
import Theorems.Thm_PositivityTheory_ThKEst_UMGS_pr_succ
import Theorems.Thm_PositivityTheory_ThKEst_UMGS_pr_zero

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
theorem _root_.solution (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G), (∀ i, Continuous (γ i)) → Continuous (pr γ) := by
  induction k with
  | zero => intro γ _; exact continuous_const.congr fun t => (pr_zero γ t).symm
  | succ k ih =>
    intro γ hγ
    refine Continuous.congr ?_ fun t => (pr_succ γ t).symm
    exact ((hγ 0).comp (continuous_ofAdd.comp (continuous_apply 0))).mul
      ((ih _ fun i => hγ i.succ).comp (continuous_pi fun i => continuous_apply _))
end PositivityTheory.ThKEst.UMGS
