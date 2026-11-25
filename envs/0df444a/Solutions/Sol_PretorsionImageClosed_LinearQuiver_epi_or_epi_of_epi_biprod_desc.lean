-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.epi_or_epi_of_epi_biprod_desc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:33:35.746807+00:00
-- url     : https://prove2.me/submissions/33f7b9f5-9eb9-42d7-8f52-d61cb4659a5b

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
public import Theorems.Thm_PretorsionImageClosed_sumSubobject_eq_right_of_le
public import Theorems.Thm_PretorsionImageClosed_sumSubobject_eq_left_of_le
public import Theorems.Thm_PretorsionImageClosed_imageSubobject_biprod_desc
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_subobject_le_or_le
public import Theorems.Thm_PretorsionImageClosed_epi_of_imageSubobject_eq_top
public import Theorems.Thm_PretorsionImageClosed_imageSubobject_eq_top_of_epi


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
    (f : Y₁ ⟶ interval k a d) (g : Y₂ ⟶ interval k a d) [Epi (biprod.desc f g)] : Epi f ∨ Epi g := by
  have himg := imageSubobject_eq_top_of_epi (biprod.desc f g)
  rw [imageSubobject_biprod_desc] at himg
  rcases subobject_le_or_le (imageSubobject f) (imageSubobject g) with h | h
  · rw [sumSubobject_eq_right_of_le h] at himg
    exact Or.inr (epi_of_imageSubobject_eq_top g himg)
  · rw [sumSubobject_eq_left_of_le h] at himg
    exact Or.inl (epi_of_imageSubobject_eq_top f himg)
end PretorsionImageClosed.LinearQuiver
