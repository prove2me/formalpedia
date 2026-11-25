-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.continuous_lu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:39.687738+00:00
-- url     : https://prove2.me/submissions/3b838bf3-5298-47d0-a081-43130e70020d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution : Continuous (lu (ι := ι) (r := r)) := by
  have hsl : ∀ (w0 : ι) (a b : Fin r), Continuous fun w : Ix ι r → ℂ => sl w w0 a b := by
    intro w0 a b
    by_cases h : b < a <;> simp [sl, h] <;> fun_prop
  have hup : ∀ (w0 : ι) (a b : Fin r), Continuous fun w : Ix ι r → ℂ => up w w0 a b := by
    intro w0 a b
    by_cases h : b < a <;> simp [up, h] <;> fun_prop
  refine continuous_pi fun i => ?_
  simp only [lu, Matrix.mul_apply, Matrix.add_apply]
  exact continuous_finset_sum _ fun k _ => (continuous_const.add (hsl _ _ _)).mul (hup _ _ _)
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
