-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.continuousOn_comp_rotAbout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:11:58.333797+00:00
-- url     : https://prove2.me/submissions/73eb4bcc-898a-4aed-b88b-a29fcdcf86bd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Circle
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_rotAbout_mem_ball_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_norm_exp_mul_I_eq_one
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_continuous_rotAbout_exp

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
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} {c : V n} {R : ℝ} {u : V n → ℂ}
    (hu : DifferentiableOn ℂ u (ball c R)) (s : Set ℝ) :
    ContinuousOn (fun p : ℝ × V n => u (rotAbout c (Complex.exp ((p.1 : ℂ) * I)) p.2))
      (s ×ˢ ball c R) := by
  refine hu.continuousOn.comp (continuous_rotAbout_exp c).continuousOn ?_
  rintro ⟨θ, z⟩ ⟨_, hz⟩
  exact (rotAbout_mem_ball_iff c (norm_exp_mul_I_eq_one θ) R z).2 hz
end ReciprocityTheory.L2DbarEstimates.C
