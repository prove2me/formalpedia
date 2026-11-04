-- Prove2me | solution 1 for ThreeSumApsp.Dominated.add_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:36.538609+00:00
-- url     : https://prove2.me/submissions/4535a766-5ef9-49fa-909f-3d7547ca0da6

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Theorems.Thm_ThreeSumApsp_Dominated_mono_right
import Theorems.Thm_ThreeSumApsp_Dominated_add

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
open ThreeSumApsp.Dominated
variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}
namespace ThreeSumApsp.Dominated
theorem _root_.solution (h₁ : Dominated dom f₁ g₁) (h₂ : Dominated dom f₂ g₂) (hg₁ : ∀ x, dom x → 0 ≤ g₁ x)
    (hg₂ : ∀ x, dom x → 0 ≤ g₂ x) : Dominated dom (fun x => f₁ x + f₂ x) fun x => g₁ x + g₂ x :=
  (h₁.mono_right fun x hx => le_add_of_nonneg_right (hg₂ x hx)).add
    (h₂.mono_right fun x hx => le_add_of_nonneg_left (hg₁ x hx))
end ThreeSumApsp.Dominated
