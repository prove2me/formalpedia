-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.div_eq_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:34:22.184117+00:00
-- url     : https://prove2.me/submissions/3354a22e-7521-4e38-acd9-f5dac217f5de

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_exists_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
open ReciprocityTheory.PGsh PowerSeries
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))
namespace ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
theorem _root_.solution {x y : K} (hy : y ≠ 0) {A B : ℝ} (hx : v x = A) (hyv : v y = B) :
    v (x / y) = ((A - B : ℝ) : WithTop ℝ) := by
  obtain ⟨c, hc⟩ := exists_real v (inv_ne_zero hy)
  have h1 : v (y * y⁻¹) = 0 := by rw [mul_inv_cancel₀ hy, v.map_one]
  rw [v.map_mul, hyv, hc, ← WithTop.coe_add] at h1
  have h2 : B + c = 0 := WithTop.coe_eq_zero.mp h1
  rw [div_eq_mul_inv, v.map_mul, hx, hc, ← WithTop.coe_add]
  congr 1
  linarith
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
