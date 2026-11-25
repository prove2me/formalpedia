-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.eq_of_retract_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:27:20.865894+00:00
-- url     : https://prove2.me/submissions/2ae37824-cc0a-41c0-a5c3-318d871db32c

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalSets
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_and_le_of_epi
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_and_le_of_mono


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
theorem _root_.solution {a d a' d' : Fin n} (had : a ≤ d) (had' : a' ≤ d')
    (h : Retract (interval k a' d') (interval k a d)) : a' = a ∧ d' = d := by
  haveI : Mono h.i := inferInstance
  haveI : Epi h.r := inferInstance
  obtain ⟨h1, h2⟩ := eq_and_le_of_mono had' h.i
  obtain ⟨h3, h4⟩ := eq_and_le_of_epi had' h.r
  exact ⟨h3, h1⟩
end PretorsionImageClosed.LinearQuiver
