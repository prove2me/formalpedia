-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.Hf_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:07:45.197788+00:00
-- url     : https://prove2.me/submissions/19af67d6-fc75-4833-99ad-9374de6b087e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfEqInner
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_eq_inner


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
theorem _root_.solution (a : EuclideanSpace ℂ ι) : Continuous fun v : EuclideanSpace ℂ ι => Hf v a := by
  simp_rw [Hf_eq_inner]
  exact continuous_const.inner continuous_id
end ReciprocityTheory.ChartRestriction.G.I2.FPw
