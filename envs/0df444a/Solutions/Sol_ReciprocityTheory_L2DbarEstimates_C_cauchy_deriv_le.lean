-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.cauchy_deriv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:02:12.432599+00:00
-- url     : https://prove2.me/submissions/debd89e2-8b70-4aa8-bd6e-1168d80fd6aa

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {g : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (closedBall c R)) (hM : ∀ w ∈ closedBall c R, ‖g w‖ ≤ M) :
    ‖deriv g c‖ ≤ M / R := by
  have hd : DiffContOnCl ℂ g (ball c R) :=
    ⟨hg.mono ball_subset_closedBall, by rw [closure_ball c hR.ne']; exact hg.continuousOn⟩
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd
    (fun w hw => hM w (sphere_subset_closedBall hw))
end ReciprocityTheory.L2DbarEstimates.C
