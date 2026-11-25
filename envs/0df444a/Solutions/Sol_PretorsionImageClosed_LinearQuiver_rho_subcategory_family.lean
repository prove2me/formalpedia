-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.rho_subcategory_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:20:46.958879+00:00
-- url     : https://prove2.me/submissions/1bf983be-af17-4b1d-a761-a612c3375427

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_lastCount_succ
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
theorem _root_.solution (D : IntervalFamily n) :
    rho (D.subcategory (k := k)).prop = D.lastCount := by
  cases n with
  | zero =>
    rw [rho_zero]
    unfold IntervalFamily.lastCount
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _
    exact p.1.elim0
  | succ m =>
    rw [rho_eq, lastCount_succ]
    apply Nat.subtype_card
    intro a
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, h⟩
      exact (D.prop_interval_iff (Fin.le_last a)).2 h
    · intro h
      exact ⟨Finset.mem_univ _, (D.prop_interval_iff (Fin.le_last a)).1 h⟩
end PretorsionImageClosed.LinearQuiver
