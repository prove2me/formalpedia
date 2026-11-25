-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paU_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:32.795523+00:00
-- url     : https://prove2.me/submissions/c35b3912-80de-4bf1-9361-081e0834d988

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaIPZeroRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_IteratedFDerivTailZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_ellL_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex Filter Topology
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution (q : ℕ) (a : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) (v : EuclideanSpace ℂ ι) :
    paU q a F v = expN 0 0 * 0 + (expN 0 0 - 1) * 0 + cexp (ellL q a v) * Pf q a F v := by
  have h0 : expN 0 0 = 1 := by simp [expN]
  rw [h0, paU, Pf, ellL_apply, Complex.exp_sub]; ring
end ReciprocityTheory.ChartRestriction.G.I2.FPw
