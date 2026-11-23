-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_cutExt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:12.735831+00:00
-- url     : https://prove2.me/submissions/485ea60f-629a-4862-bae8-01ccc8b14dd2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff Classical
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (χ : ℝ → ℝ) (ε : ℝ)
    (hcont : Continuous (ev n g ph r)) (hχ0 : ∀ t, 1 ≤ t → χ t = 0) (hε : 0 < ε) (x : M)
    (hx : ε ^ 2 < ev n g ph r x) :
    cutExt n z g ph r c W χ ε =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds hx] with y hy
  simp only [cutExt]
  rw [hχ0 _ ((one_le_div (by positivity)).2 hy.le)]
  simp
end ReciprocityTheory.L2DbarEstimates.I
