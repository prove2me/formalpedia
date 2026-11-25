-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.ofIntervals_prop_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:32:44.778176+00:00
-- url     : https://prove2.me/submissions/9bbff744-b99b-4efc-a942-ee0d7c4c6162

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalSets
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_of_retract_interval

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
theorem _root_.solution (S : Fin n → Fin n → Prop) {a d : Fin n} (had : a ≤ d) :
    (ofIntervals (k := k) S).prop (interval k a d) ↔ S a d := by
  constructor
  · intro h
    exact h a d had (Retract.refl _)
  · intro h a' d' had' h'
    obtain ⟨rfl, rfl⟩ := eq_of_retract_interval had had' h'
    exact h
end PretorsionImageClosed.LinearQuiver
