-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.suffix_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:13:10.569664+00:00
-- url     : https://prove2.me/submissions/82c3b9b2-3689-4b9b-a36e-2288913e8c15

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_intervalIncl
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_id
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
theorem _root_.solution (a d : Fin n) : suffix (k := k) a d a le_rfl = ⊤ := by
  rw [suffix]
  have : intervalIncl k d (le_refl a) = 𝟙 _ := hom_ext_coord fun i => by
    rw [coord_intervalIncl, coord_id]
  have h2 : IsIso (intervalIncl k d (le_refl a)) := by rw [this]; infer_instance
  exact Subobject.mk_eq_top_of_isIso _
end PretorsionImageClosed.LinearQuiver
