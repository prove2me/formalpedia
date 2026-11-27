-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.factorization_factorial_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:09.872091+00:00
-- url     : https://prove2.me/submissions/94d237b0-ee77-467c-84a5-f174f702def5

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) :
    (p ^ 2).factorial.factorization p = p + 1 := by
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp,
    padicValNat_factorial (p := p) (n := p ^ 2) (b := 3) (by rw [Nat.log_pow hp.one_lt]; norm_num)]
  have h1 : p ^ 2 / p ^ 1 = p := by rw [pow_one, pow_two, Nat.mul_div_cancel _ hp.pos]
  have h2 : p ^ 2 / p ^ 2 = 1 := Nat.div_self (pow_pos hp.pos 2)
  rw [show Finset.Ico 1 3 = {1, 2} by decide, Finset.sum_pair (by norm_num), h1, h2]
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
