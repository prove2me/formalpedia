-- Prove2me | solution 1 for ThreeSumApsp.dominated_iff_isBigO_principal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:24.759248+00:00
-- url     : https://prove2.me/submissions/d25fa4e9-2721-49b5-b1a7-8ea0171e2565

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Theorems.Thm_ThreeSumApsp_Dominated_of_exists_const

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
open ThreeSumApsp.Dominated
variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}
namespace ThreeSumApsp.Dominated
namespace _root_.ThreeSumApsp
theorem _root_.solution (hf : ∀ x, dom x → 0 ≤ f x)
    (hg : ∀ x, dom x → 0 ≤ g x) : Dominated dom f g ↔ f =O[𝓟 {x | dom x}] g := by
  have hnorm : ∀ (C : ℝ) x, dom x → (‖f x‖ ≤ C * ‖g x‖ ↔ f x ≤ C * g x) := fun C x hx => by
    rw [Real.norm_of_nonneg (hf x hx), Real.norm_of_nonneg (hg x hx)]
  rw [isBigO_principal]
  exact ⟨fun ⟨C, _, h⟩ => ⟨C, fun x hx => (hnorm C x hx).2 (h x hx)⟩,
    fun ⟨C, h⟩ => of_exists_const ⟨C, fun x hx => (hnorm C x hx).1 (h x hx)⟩ hg⟩
end _root_.ThreeSumApsp
end ThreeSumApsp.Dominated
