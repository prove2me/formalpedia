-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.coeff_subst_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:28:49.699909+00:00
-- url     : https://prove2.me/submissions/5a8c7a54-0f17-4aa2-a8e8-9c5733c4f121

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_coeff_pow_gap

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
variable {K : Type*} [Field K]
namespace ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
theorem _root_.solution (lg P : PowerSeries K) (M : ℕ) (hM : 2 ≤ M) (b : K)
    (hl0 : coeff 0 lg = 0) (hl1 : coeff 1 lg = 1) (hlg : ∀ j, 2 ≤ j → j < M → coeff j lg = 0)
    (hP0 : coeff 0 P = 0) (hP1 : coeff 1 P = b) (hPg : ∀ j, 2 ≤ j → j < M → coeff j P = 0) :
    coeff M (subst P lg) = coeff M P + coeff M lg * b ^ M := by
  have hs : HasSubst P :=
    HasSubst.of_constantCoeff_zero' (by rw [← coeff_zero_eq_constantCoeff_apply]; exact hP0)
  rw [coeff_subst' hs]
  have hsupp : (Function.support fun d : ℕ => coeff d lg • coeff M (P ^ d)) ⊆
      ↑(Finset.range (M + 1)) := by
    intro d hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    simp only
    rw [coeff_pow_gap P M hM b hP0 hP1 hPg d (by omega), if_neg (by omega), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_range_succ,
    Finset.sum_eq_single 1]
  · rw [coeff_pow_gap P M hM b hP0 hP1 hPg M hM, if_pos rfl]
    simp [hl1]
  · intro d hd hd1
    rcases Nat.lt_or_ge d 2 with h | h
    · have : d = 0 := by omega
      subst this; rw [hl0, zero_smul]
    · rw [hlg d h (Finset.mem_range.mp hd), zero_smul]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
