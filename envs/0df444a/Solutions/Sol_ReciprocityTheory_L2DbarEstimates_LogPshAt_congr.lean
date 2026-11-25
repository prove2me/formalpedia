-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.LogPshAt.congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:49:02.305967+00:00
-- url     : https://prove2.me/submissions/b0c84f2e-598c-4477-9a54-128fd97a9870

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
namespace LogPshAt
theorem _root_.solution {u w : V n → ℝ} {x : V n} (h : u =ᶠ[𝓝 x] w) (hu : LogPshAt n u x) :
    LogPshAt n w x := by
  have hc : (fun y => (u y : ℂ)) =ᶠ[𝓝 x] fun y => (w y : ℂ) := h.fun_comp (fun t : ℝ => (t : ℂ))
  obtain ⟨h0, h1⟩ := hu
  refine ⟨h.eq_of_nhds ▸ h0, fun ξ => ?_⟩
  rw [← leviV_congr hc ξ, ← h.eq_of_nhds]
  simp only [← wd_congr hc]
  exact h1 ξ
end LogPshAt
end ReciprocityTheory.L2DbarEstimates
