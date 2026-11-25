-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals.fac_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:57.171233+00:00
-- url     : https://prove2.me/submissions/a3cc8568-e776-4ebc-943c-23866338831a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SlowWeightBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals
namespace ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals
theorem _root_.solution {A b t β β' R : ℝ} (hR : 0 < R) (hA : R ≤ A) (ht : 0 ≤ t) (hβ : |β| ≤ R)
    (hβ' : |β'| ≤ R) :
    (A ^ 2 + (β - b) ^ 2) ^ (-t / 2) ≤ 3 ^ t * (A ^ 2 + (β' - b) ^ 2) ^ (-t / 2) := by
  have hA0 : 0 < A := lt_of_lt_of_le hR hA
  have hx : 0 < A ^ 2 + (β - b) ^ 2 := by positivity
  have hy : 0 < A ^ 2 + (β' - b) ^ 2 := by positivity
  have h1 := abs_le.1 hβ
  have h2 := abs_le.1 hβ'
  have hd : (β' - β) ^ 2 ≤ 4 * A ^ 2 := by nlinarith
  have h9 : A ^ 2 + (β' - b) ^ 2 ≤ 9 * (A ^ 2 + (β - b) ^ 2) := by
    nlinarith [sq_nonneg ((β' - β) - (β - b))]
  calc (A ^ 2 + (β - b) ^ 2) ^ (-t / 2)
      = 3 ^ t * (9 * (A ^ 2 + (β - b) ^ 2)) ^ (-t / 2) := by
        rw [Real.mul_rpow (by norm_num) hx.le, show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num), ← mul_assoc, ← Real.rpow_add (by norm_num)]
        have h0 : t + 2 * (-t / 2) = 0 := by ring
        rw [h0, Real.rpow_zero, one_mul]
    _ ≤ 3 ^ t * (A ^ 2 + (β' - b) ^ 2) ^ (-t / 2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hy h9 (by linarith)) (by positivity)
end ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals
