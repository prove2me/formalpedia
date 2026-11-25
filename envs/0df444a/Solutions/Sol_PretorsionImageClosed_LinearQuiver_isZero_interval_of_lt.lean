-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.isZero_interval_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:15:22.163616+00:00
-- url     : https://prove2.me/submissions/8cd275e1-cdb5-4a5c-b655-42a7b899abae

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_isZero_interval_obj_of_not_mem


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
theorem _root_.solution {ℓ d : Fin n} (h : d < ℓ) : IsZero (interval k ℓ d) :=
  Functor.isZero _ fun i => isZero_interval_obj_of_not_mem k fun hi => (h.trans_le hi.1).not_ge hi.2
end PretorsionImageClosed.LinearQuiver
