-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.norm_le_of_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:10.197484+00:00
-- url     : https://prove2.me/submissions/be977938-e7f2-41e0-a885-2c5e3a8f936f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_IteratedDerivZeroOfBound

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution {q : ℂ → ℂ} (hq : Differentiable ℂ q) {r : ℕ} {M : ℝ}
    (hM : ∀ w : ℂ, ‖w‖ = 1 → ‖w ^ r * q w‖ ≤ M) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖q z‖ ≤ M := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) 1) isBounded_ball
    hq.diffContOnCl (fun w hw => ?_) ?_
  · rw [frontier_ball 0 one_ne_zero, mem_sphere_zero_iff_norm] at hw
    have := hM w hw
    rwa [norm_mul, norm_pow, hw, one_pow, one_mul] at this
  · rw [closure_ball 0 one_ne_zero, mem_closedBall_zero_iff]; exact hz
end PositivityTheory.Rg.Sw.SP
