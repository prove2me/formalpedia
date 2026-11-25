-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:00:54.627474+00:00
-- url     : https://prove2.me/submissions/1d57f2c5-2f21-4041-9a0f-f74c44c70936

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_nsmul_one_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_natCast_eq_zero_of_coprime

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hp1 : v (p : K) = 1) {m : ℕ}
    (hm : m ≠ 0) : v (m : K) = ((m.factorization p : ℝ) : WithTop ℝ) := by
  have e := Nat.ordProj_mul_ordCompl_eq_self m p
  have hc := Nat.coprime_ordCompl hp hm
  conv_lhs => rw [← e]
  rw [Nat.cast_mul, Nat.cast_pow, v.map_mul, v.map_pow, hp1,
    natCast_eq_zero_of_coprime v hp1 hc, add_zero, nsmul_one_coe]
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
