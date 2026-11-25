-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.exists_interval_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:39:50.448828+00:00
-- url     : https://prove2.me/submissions/8ce4c274-5b50-4ba5-bd17-e11b49475cec

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_and_le_of_mono
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_intervalSum
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_mono_or_mono_of_mono_biprod_lift
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
    {Y : Statement.LinRep k n} (hY : C.prop Y) (i : interval k a b ⟶ Y) [Mono i] :
    ∃ c : Fin n, c ≤ a ∧ C.prop (interval k c b) := by
  induction intervalSum Y with
  | zero hz =>
    exfalso
    exact not_isZero_interval hab (IsZero.of_mono i hz)
  | @step Y Y' c e hce h' e' ih =>
    have hY' : C.prop Y' := C.prop_biprod_right (C.prop_of_iso e' hY)
    have hM : C.prop (interval k c e) := C.prop_biprod_left (C.prop_of_iso e' hY)
    have hmono : Mono (biprod.lift (i ≫ e'.hom ≫ biprod.fst) (i ≫ e'.hom ≫ biprod.snd)) := by
      have : biprod.lift (i ≫ e'.hom ≫ biprod.fst) (i ≫ e'.hom ≫ biprod.snd) = i ≫ e'.hom := by
        apply biprod.hom_ext <;> simp
      rw [this]
      exact mono_comp _ _
    rcases mono_or_mono_of_mono_biprod_lift
        (i ≫ e'.hom ≫ (biprod.fst : interval k c e ⊞ Y' ⟶ interval k c e))
        (i ≫ e'.hom ≫ (biprod.snd : interval k c e ⊞ Y' ⟶ Y')) with hf | hg
    · obtain ⟨rfl, hca⟩ := eq_and_le_of_mono hab
        (i ≫ e'.hom ≫ (biprod.fst : interval k c e ⊞ Y' ⟶ interval k c e))
      exact ⟨c, hca, hM⟩
    · exact ih hY' (i ≫ e'.hom ≫ (biprod.snd : interval k c e ⊞ Y' ⟶ Y'))
end PretorsionImageClosed.LinearQuiver
