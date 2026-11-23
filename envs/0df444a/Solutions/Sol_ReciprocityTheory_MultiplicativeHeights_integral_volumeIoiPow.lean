-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.integral_volumeIoiPow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:26.056542+00:00
-- url     : https://prove2.me/submissions/dded441e-c59f-481d-9e75-a45612fe9129

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric Set Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (k : ℕ) (g : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), g r ∂(Measure.volumeIoiPow k) = ∫ r in Ioi (0 : ℝ), r ^ k * g r := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r ^ k * g r)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) k)]
end ReciprocityTheory.MultiplicativeHeights
