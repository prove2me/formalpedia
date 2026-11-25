-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.le_of_coord_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:17:48.34581+00:00
-- url     : https://prove2.me/submissions/2a99b5eb-5d5a-401b-ac0a-01448e667650

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Theorems.Thm_P2M_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_lt__ddf324dfd620
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_lt


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
theorem _root_.solution {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) {i : Fin n}
    (h : coord η i ≠ 0) : a ≤ c ∧ b ≤ d := by
  constructor
  · by_contra hca
    exact h (coord_eq_zero_of_lt' η (not_le.1 hca) i)
  · by_contra hbd
    exact h (coord_eq_zero_of_lt η (not_le.1 hbd) i)
end PretorsionImageClosed.LinearQuiver
