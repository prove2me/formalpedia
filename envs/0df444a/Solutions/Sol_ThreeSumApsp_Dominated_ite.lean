-- Prove2me | solution 1 for ThreeSumApsp.Dominated.ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:37.849407+00:00
-- url     : https://prove2.me/submissions/3eb6fae3-4fc0-49a6-bccb-2936af16d10f

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Theorems.Thm_ThreeSumApsp_Dominated_trans

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
open ThreeSumApsp.Dominated
variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}
namespace ThreeSumApsp.Dominated
theorem _root_.solution {p : α → Prop} [DecidablePred p]
    (h₁ : Dominated (fun x => dom x ∧ p x) f₁ g) (h₂ : Dominated (fun x => dom x ∧ ¬p x) f₂ g)
    (hg : ∀ x, dom x → 0 ≤ g x) : Dominated dom (fun x => if p x then f₁ x else f₂ x) g := by
  obtain ⟨C, hC, h₁⟩ := h₁
  obtain ⟨D, hD, h₂⟩ := h₂
  refine ⟨C + D, add_nonneg hC hD, fun x hx => ?_⟩
  change (if p x then f₁ x else f₂ x) ≤ (C + D) * g x
  split_ifs with hp
  · exact (h₁ x ⟨hx, hp⟩).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (hg x hx))
  · exact (h₂ x ⟨hx, hp⟩).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (hg x hx))
end ThreeSumApsp.Dominated
