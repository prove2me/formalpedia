-- Prove2me | solution 1 for ThreeSumApsp.Dominated.mul_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:15:06.379212+00:00
-- url     : https://prove2.me/submissions/9c923976-05d6-433c-b84f-220cefed6507

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Theorems.Thm_ThreeSumApsp_Dominated_const_mul

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
open ThreeSumApsp.Dominated
variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}
namespace ThreeSumApsp.Dominated
theorem _root_.solution (hfg : Dominated dom f g) {c : ℝ} (hc : 0 ≤ c) :
    Dominated dom (fun x => f x * c) g := by
  simpa only [mul_comm] using hfg.const_mul hc
end ThreeSumApsp.Dominated
