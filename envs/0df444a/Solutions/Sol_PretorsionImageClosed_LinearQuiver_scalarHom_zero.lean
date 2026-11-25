-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.scalarHom_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:08:41.360159+00:00
-- url     : https://prove2.me/submissions/5073256a-2061-4d57-a265-3e2742790506

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_zero
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_hom_ext_coord


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
theorem _root_.solution (a d : Fin n) : scalarHom a d (0 : k) = 0 :=
  hom_ext_coord fun i => by rw [coord_scalarHom, zero_mul, coord_zero (k := k) a d a d i]
end PretorsionImageClosed.LinearQuiver
