-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.rho_subcategory
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:29:50.086972+00:00
-- url     : https://prove2.me/submissions/98e3b8d8-23ec-41ee-9b0c-31d01a4ac89c

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffCriterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_rho_eq
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_rho_zero


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (β : RowCutoff n) :
    rho (β.subcategory (k := k)).prop = β.rowsReaching := by
  cases n with
  | zero =>
    rw [rho_zero]
    simp [RowCutoff.rowsReaching]
  | succ m =>
    rw [rho_eq, RowCutoff.rowsReaching]
    apply Nat.subtype_card
    intro a
    rw [Finset.mem_filter, β.prop_interval_iff (Fin.le_last a), Fin.val_last]
    have h1 := β.β_le a
    constructor
    · rintro ⟨-, h⟩
      omega
    · intro h
      exact ⟨Finset.mem_univ _, by omega⟩
end PretorsionImageClosed.LinearQuiver
