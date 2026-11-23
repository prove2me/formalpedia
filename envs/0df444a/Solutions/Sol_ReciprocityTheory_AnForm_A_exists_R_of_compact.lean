-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.exists_R_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:12.341369+00:00
-- url     : https://prove2.me/submissions/27f81040-20d0-43b1-8646-8850acb07ebb

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open GreenFunction
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {F : Type} [NormedAddCommGroup F] {u : F → ℝ}
    (hc : HasCompactSupport u) : ∃ R > 0, ∀ q, q ∈ tsupport u → ‖q‖ ≤ R := by
  obtain ⟨R0, hR0⟩ := (Metric.isBounded_iff_subset_closedBall (0 : F)).1 hc.isCompact.isBounded
  refine ⟨max R0 0 + 1, by positivity, fun q hq => ?_⟩
  have := hR0 hq
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left R0 0]
end ReciprocityTheory.AnForm.A
