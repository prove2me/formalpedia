-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.reject_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:33:27.523393+00:00
-- url     : https://prove2.me/submissions/f01b0bc8-1f96-418e-bd2e-cf228e22a277

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Theorems.Thm_PretorsionImageClosed_Subobject_exists_minimal_of_nonempty


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [Abelian C]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (T : Subcategory C) (X : C)
variable (F : Subcategory C)
variable [HasLength C]
variable {T X}
variable (X)
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution :
    F.reject X ∈ F.quotientsIn X ∧
      ∀ K ∈ F.quotientsIn X, K ≤ F.reject X → K = F.reject X :=
  Classical.choose_spec
    (Subobject.exists_minimal_of_nonempty (F.quotientsIn X) ⟨⊤, F.top_mem_quotientsIn X⟩)
end PretorsionImageClosed.Statement.Subcategory
