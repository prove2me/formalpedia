-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.intervalSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:37.560922+00:00
-- url     : https://prove2.me/submissions/26d30b42-1844-4280-b35f-1b64d3367729

module
public import Definitions.Def_PretorsionImageClosed_Biproducts_Basic
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_not_isZero_interval
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_exists_iso_biprod_interval
public import Theorems.Thm_PretorsionImageClosed_isZero_of_isIso_biprod_inr
public import Theorems.Thm_PretorsionImageClosed_length_lt_of_mono


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (X : Statement.LinRep k n) : IntervalSum X := by
  suffices h : ∀ m, ∀ Y : Statement.LinRep k n, length Y = m → IntervalSum Y from h _ X rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro Y hY
    by_cases hz : IsZero Y
    · exact IntervalSum.zero hz
    obtain ⟨a, d, had, Y', ⟨e⟩⟩ := exists_iso_biprod_interval Y hz
    have hmono : Mono (biprod.inr ≫ e.inv : Y' ⟶ Y) := mono_comp _ _
    have hnotiso : ¬ IsIso (biprod.inr ≫ e.inv : Y' ⟶ Y) := by
      intro hiso
      have : IsIso (biprod.inr : Y' ⟶ interval k a d ⊞ Y') := by
        have h2 : (biprod.inr : Y' ⟶ interval k a d ⊞ Y') = (biprod.inr ≫ e.inv) ≫ e.hom := by
          simp
        rw [h2]
        infer_instance
      exact not_isZero_interval had (isZero_of_isIso_biprod_inr this)
    have hlt : length Y' < length Y := length_lt_of_mono _ hnotiso
    exact IntervalSum.step a d had (ih _ (hY ▸ hlt) Y' rfl) e
end PretorsionImageClosed.LinearQuiver
