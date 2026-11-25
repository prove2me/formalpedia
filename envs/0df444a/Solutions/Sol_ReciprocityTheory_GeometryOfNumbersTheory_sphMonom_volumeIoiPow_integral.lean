-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_volumeIoiPow_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:07.769209+00:00
-- url     : https://prove2.me/submissions/191db718-6593-4821-8356-bff39e099083

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Metric Set
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (m : ℕ) (φ : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), φ r ∂(Measure.volumeIoiPow m) = ∫ r in Ioi (0 : ℝ), r ^ m * φ r := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul
    ((measurable_subtype_coe.pow_const m).ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [integral_subtype_comap measurableSet_Ioi (fun r : ℝ => (ENNReal.ofReal (r ^ m)).toReal • φ r)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hr) m)]
end ReciprocityTheory.GeometryOfNumbersTheory
