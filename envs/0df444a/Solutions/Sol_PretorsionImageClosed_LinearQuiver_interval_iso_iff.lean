-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.interval_iso_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:49.441355+00:00
-- url     : https://prove2.me/submissions/fbed82ee-e86b-4c09-97d2-dc7ea09f0371

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_finrank_obj_eq_of_iso
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_finrank_intervalSpace


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
theorem _root_.solution {a d a' d' : Fin n} (had : a ≤ d) (had' : a' ≤ d') :
    Nonempty (interval k a d ≅ interval k a' d') ↔ a = a' ∧ d = d' := by
  constructor
  · rintro ⟨e⟩
    have h : ∀ i, (if a ≤ i ∧ i ≤ d then (1 : ℕ) else 0) = if a' ≤ i ∧ i ≤ d' then 1 else 0 := by
      intro i
      have := finrank_obj_eq_of_iso e i
      change Module.finrank k (intervalSpace k a d i) = Module.finrank k (intervalSpace k a' d' i)
        at this
      rwa [finrank_intervalSpace, finrank_intervalSpace] at this
    have hmem : ∀ i, (a ≤ i ∧ i ≤ d) ↔ (a' ≤ i ∧ i ≤ d') := by
      intro i
      have hi := h i
      constructor
      · intro hi1
        by_contra hi2
        rw [if_pos hi1, if_neg hi2] at hi
        exact one_ne_zero hi
      · intro hi2
        by_contra hi1
        rw [if_neg hi1, if_pos hi2] at hi
        exact zero_ne_one hi
    have ha := (hmem a).1 ⟨le_rfl, had⟩
    have ha' := (hmem a').2 ⟨le_rfl, had'⟩
    have hd := (hmem d).1 ⟨had, le_rfl⟩
    have hd' := (hmem d').2 ⟨had', le_rfl⟩
    exact ⟨le_antisymm ha'.1 ha.1, le_antisymm hd.2 hd'.2⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨Iso.refl _⟩
end PretorsionImageClosed.LinearQuiver
