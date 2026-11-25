-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.exists_iso_interval_of_indecomposable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:41.967478+00:00
-- url     : https://prove2.me/submissions/36bea0ed-918e-462b-be84-9a4d218c33a3

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_exists_iso_biprod_interval
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_not_isZero_interval


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
theorem _root_.solution {X : Statement.LinRep k n} (hX : Indecomposable X) :
    ∃ a d : Fin n, a ≤ d ∧ Nonempty (X ≅ interval k a d) := by
  obtain ⟨a, d, had, X', ⟨e⟩⟩ := exists_iso_biprod_interval X hX.1
  rcases hX.2 _ _ e with h | h
  · exact absurd h (not_isZero_interval had)
  · exact ⟨a, d, had, ⟨e ≪≫ (isoBiprodZero h).symm⟩⟩
end PretorsionImageClosed.LinearQuiver
