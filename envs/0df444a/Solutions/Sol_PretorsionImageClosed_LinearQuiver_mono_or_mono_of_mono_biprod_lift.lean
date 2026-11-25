-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.mono_or_mono_of_mono_biprod_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:33:56.617448+00:00
-- url     : https://prove2.me/submissions/0f79fee7-84b5-454a-9af9-7d7981739332

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
public import Theorems.Thm_PretorsionImageClosed_kernelSubobject_biprod_lift
public import Theorems.Thm_PretorsionImageClosed_mono_of_kernelSubobject_eq_bot
public import Theorems.Thm_PretorsionImageClosed_kernelSubobject_eq_bot_of_mono
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_subobject_le_or_le

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
theorem _root_.solution {a d : Fin n} {Y₁ Y₂ : Statement.LinRep k n}
    (f : interval k a d ⟶ Y₁) (g : interval k a d ⟶ Y₂) [Mono (biprod.lift f g)] :
    Mono f ∨ Mono g := by
  have hker := kernelSubobject_eq_bot_of_mono (biprod.lift f g)
  rw [kernelSubobject_biprod_lift] at hker
  rcases subobject_le_or_le (kernelSubobject f) (kernelSubobject g) with h | h
  · rw [inf_eq_left.2 h] at hker
    exact Or.inl (mono_of_kernelSubobject_eq_bot f hker)
  · rw [inf_eq_right.2 h] at hker
    exact Or.inr (mono_of_kernelSubobject_eq_bot g hker)
end PretorsionImageClosed.LinearQuiver
