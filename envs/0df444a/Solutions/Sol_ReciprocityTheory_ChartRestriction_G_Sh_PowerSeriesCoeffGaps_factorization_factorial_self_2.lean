-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.factorization_factorial_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:04.653713+00:00
-- url     : https://prove2.me/submissions/b6f4e883-4692-4bbc-8012-2d257ece4e4d

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
    p.factorial.factorization p = 1 := by
  have := Fact.mk hp
  have hl : Nat.log p p = 1 := by
    have := Nat.log_pow hp.one_lt 1
    rwa [pow_one] at this
  rw [Nat.factorization_def _ hp,
    padicValNat_factorial (p := p) (n := p) (b := 2) (by rw [hl]; norm_num)]
  rw [show Finset.Ico 1 2 = {1} by decide, Finset.sum_singleton, pow_one, Nat.div_self hp.pos]
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
