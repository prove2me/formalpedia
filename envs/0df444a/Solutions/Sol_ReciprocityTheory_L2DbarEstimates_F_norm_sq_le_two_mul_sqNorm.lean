-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.norm_sq_le_two_mul_sqNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:30:03.344203+00:00
-- url     : https://prove2.me/submissions/69e7d8e2-e8c3-4502-95e9-61e737840d93

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_sqNorm_entry_le_two_mul

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
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (σ : Fin n → Fin n → ℂ) : ‖σ‖ ^ 2 ≤ 2 * sq2 n σ := by
  have h0 : 0 ≤ 2 * sq2 n σ := by
    unfold sq2
    positivity
  have hb : ‖σ‖ ≤ Real.sqrt (2 * sq2 n σ) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun k => ?_
    simpa using Real.abs_le_sqrt (sqNorm_entry_le_two_mul σ j k)
  calc ‖σ‖ ^ 2 ≤ (Real.sqrt (2 * sq2 n σ)) ^ 2 := by gcongr
    _ = 2 * sq2 n σ := Real.sq_sqrt h0
end ReciprocityTheory.L2DbarEstimates.F
