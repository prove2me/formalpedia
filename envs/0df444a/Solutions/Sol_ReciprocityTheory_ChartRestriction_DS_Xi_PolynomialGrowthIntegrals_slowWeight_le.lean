-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals.slowWeight_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:25:21.612805+00:00
-- url     : https://prove2.me/submissions/4beb1217-99e1-4385-889e-828eb46efc95

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SlowWeightBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_PolynomialGrowthIntegrals_fac_le

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
theorem _root_.solution {n : ℕ} {t A b : Fin n → ℝ} {R β β' : ℝ} (hR : 0 < R) (ht : ∀ i, 0 ≤ t i)
    (hA : ∀ i, R ≤ A i) (hβ : |β| ≤ R) (hβ' : |β'| ≤ R) :
    slowly t A b β ≤ ENNReal.ofReal (3 ^ ∑ i, t i) * slowly t A b β' := by
  unfold slowly
  rw [Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 3),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun i _ => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (fac_le hR (hA i) (ht i) hβ hβ')
end ReciprocityTheory.ChartRestriction.DS.Xi.PolynomialGrowthIntegrals
