-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.subobject_le_or_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:25:02.191193+00:00
-- url     : https://prove2.me/submissions/ef3438b0-1863-4df9-b399-e2fc74f17a04

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_bot_or_eq_suffix
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_suffix_le_or_le
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_bot_le


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {a d : Fin n} (K K' : Subobject (interval k a d)) : K ≤ K' ∨ K' ≤ K := by
  rcases eq_bot_or_eq_suffix K with rfl | ⟨ℓ, hal, -, rfl⟩
  · exact Or.inl bot_le
  rcases eq_bot_or_eq_suffix K' with rfl | ⟨ℓ', hal', -, rfl⟩
  · exact Or.inr bot_le
  exact suffix_le_or_le hal hal'
end PretorsionImageClosed.LinearQuiver
