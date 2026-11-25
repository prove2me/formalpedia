-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.gN_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:08:09.450338+00:00
-- url     : https://prove2.me/submissions/4b66b740-6e74-489a-8d21-652792dd0f75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaIPZeroRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_IteratedFDerivTailZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem

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
theorem _root_.solution (z : ℂ) : Tendsto (fun N => gN N z) atTop (𝓝 0) := by
  unfold gN
  have h := (NormedSpace.expSeries_div_hasSum_exp z).tendsto_sum_nat
  rw [← Complex.exp_eq_exp_ℂ] at h
  have h2 : Tendsto (fun N => expN N z) atTop (𝓝 (cexp z)) := by
    unfold expN
    exact h.comp (tendsto_add_atTop_nat 1)
  have h3 := (tendsto_const_nhds (x := cexp z)).sub h2
  rw [sub_self] at h3
  exact h3
end ReciprocityTheory.ChartRestriction.G.I2.FPw
