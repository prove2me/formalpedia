-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.canonicalHom_le_rfl_eq_intervalIncl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:16:19.634392+00:00
-- url     : https://prove2.me/submissions/c336658f-d570-4da4-80ad-1fd2328a7839

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_intervalIncl
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_canonicalHom
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
theorem _root_.solution {a c d : Fin n} (hac : a ≤ c) :
    canonicalHom (k := k) hac (le_refl d) = intervalIncl k d hac :=
  hom_ext_coord fun i => by rw [coord_canonicalHom, coord_intervalIncl]
end PretorsionImageClosed.LinearQuiver
