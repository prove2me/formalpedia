-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.not_isZero_interval_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:16:11.636862+00:00
-- url     : https://prove2.me/submissions/f04e8aed-a5dc-4a46-b52e-9688d788ee7a

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
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
theorem _root_.solution {a d : Fin n} (h : a ≤ d) : ¬ IsZero (interval k a d) :=
  not_isZero_interval h
end PretorsionImageClosed.LinearQuiver
