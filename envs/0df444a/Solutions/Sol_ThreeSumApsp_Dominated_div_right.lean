-- Prove2me | solution 1 for ThreeSumApsp.Dominated.div_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:50.249457+00:00
-- url     : https://prove2.me/submissions/8f765d1b-34d9-453d-8e21-9ff058e27e1d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Theorems.Thm_ThreeSumApsp_Dominated_mul_right

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
open ThreeSumApsp.Dominated
variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}
namespace ThreeSumApsp.Dominated
theorem _root_.solution (hfg : Dominated dom f g) (hk : ∀ x, dom x → 0 ≤ k x) :
    Dominated dom (fun x => f x / k x) fun x => g x / k x := by
  simpa only [div_eq_mul_inv] using hfg.mul_right fun x hx => inv_nonneg.2 (hk x hx)
end ThreeSumApsp.Dominated
