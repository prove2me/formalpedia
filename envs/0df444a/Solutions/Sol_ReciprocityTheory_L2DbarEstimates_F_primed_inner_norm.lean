-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.primed_inner_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:30:12.669802+00:00
-- url     : https://prove2.me/submissions/051e8aec-7ff5-4fbd-bb8c-4d259859869e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Primed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) (F0 : M → ℂ)
    (g : M → V n) (x : M) :
    ‖⟪dbarF n z F0 x, g x⟫_ℂ‖ = ‖dbarDot n z F0 x (fun j => g x j)‖ := by
  have : ⟪dbarF n z F0 x, g x⟫_ℂ = starRingEnd ℂ (dbarDot n z F0 x (fun j => g x j)) := by
    simp [dbarF, dbarDot, PiLp.inner_apply, map_sum, mul_comm]
  rw [this, Complex.norm_conj]
end ReciprocityTheory.L2DbarEstimates.F
