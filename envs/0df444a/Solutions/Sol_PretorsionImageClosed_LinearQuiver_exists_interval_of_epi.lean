-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.exists_interval_of_epi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:38:45.020827+00:00
-- url     : https://prove2.me/submissions/375fe752-dad0-4e39-9e4d-0db816822ce6

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_epi_or_epi_of_epi_biprod_desc
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_and_le_of_epi
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_intervalSum
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_not_isZero_interval
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_biprod_left
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_biprod_right


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
theorem _root_.solution (C : Subcategory (Statement.LinRep k n)) {a b : Fin n} (hab : a ≤ b)
    {X : Statement.LinRep k n} (hX : C.prop X) (p : X ⟶ interval k a b) [Epi p] :
    ∃ d : Fin n, b ≤ d ∧ C.prop (interval k a d) := by
  induction intervalSum X with
  | zero hz =>
    exfalso
    exact not_isZero_interval hab (hz.of_epi p)
  | @step X X' c e hce h' e' ih =>
    have hX' : C.prop X' := C.prop_biprod_right (C.prop_of_iso e' hX)
    have hM : C.prop (interval k c e) := C.prop_biprod_left (C.prop_of_iso e' hX)
    -- `e'.inv ≫ p : M_{c,e} ⊞ X' ⟶ M_{a,b}` is an epimorphism, a `biprod.desc`
    have hepi : Epi (biprod.desc (biprod.inl ≫ e'.inv ≫ p) (biprod.inr ≫ e'.inv ≫ p)) := by
      have : biprod.desc (biprod.inl ≫ e'.inv ≫ p) (biprod.inr ≫ e'.inv ≫ p) = e'.inv ≫ p := by
        apply biprod.hom_ext' <;> simp
      rw [this]
      exact epi_comp _ _
    rcases epi_or_epi_of_epi_biprod_desc
        ((biprod.inl : interval k c e ⟶ interval k c e ⊞ X') ≫ e'.inv ≫ p)
        ((biprod.inr : X' ⟶ interval k c e ⊞ X') ≫ e'.inv ≫ p) with hf | hg
    · obtain ⟨rfl, hbe⟩ := eq_and_le_of_epi hab
        ((biprod.inl : interval k c e ⟶ interval k c e ⊞ X') ≫ e'.inv ≫ p)
      exact ⟨e, hbe, hM⟩
    · exact ih hX' ((biprod.inr : X' ⟶ interval k c e ⊞ X') ≫ e'.inv ≫ p)
end PretorsionImageClosed.LinearQuiver
