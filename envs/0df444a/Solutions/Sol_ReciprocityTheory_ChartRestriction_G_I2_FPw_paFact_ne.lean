-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paFact_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:08:42.9734+00:00
-- url     : https://prove2.me/submissions/090cb0e2-113f-47e8-8a01-3368e408b363

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaIPZeroRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution (α : ι →₀ ℕ) : (paFact α : ℂ) ≠ 0 := by
  unfold paFact
  exact Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => Nat.factorial_ne_zero _)
end ReciprocityTheory.ChartRestriction.G.I2.FPw
