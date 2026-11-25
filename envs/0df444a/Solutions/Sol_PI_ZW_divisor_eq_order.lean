-- Prove2me | solution 1 for PI.ZW.divisor_eq_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:16:27.181188+00:00
-- url     : https://prove2.me/submissions/1a222128-b9f8-48a2-9464-ba98a9e4f4a2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Jensen
import Theorems.Thm_PI_ZW_order_ne_top_of_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric
open PI PI.ZW
namespace PI.ZW
theorem _root_.solution {f : ℂ → ℂ} {c z : ℂ} {r R : ℝ} (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hfc : f c ≠ 0) (hrR : r ≤ R) (hz : z ∈ closedBall c r) :
    MeromorphicOn.divisor f (closedBall c r) z = (analyticOrderNatAt f z : ℤ) := by
  have hzR : z ∈ closedBall c R := closedBall_subset_closedBall hrR hz
  have hm : MeromorphicOn f (closedBall c r) := (hf.mono (closedBall_subset_closedBall hrR)).meromorphicOn
  have hne := order_ne_top_of_ball hf hfc hzR
  rw [MeromorphicOn.divisor_apply hm hz, (hf z hzR).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hne]
  simp
end PI.ZW
