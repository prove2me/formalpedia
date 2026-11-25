-- Prove2me | solution 1 for PretorsionImageClosed.imageSubobject_arrow_comp_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:19:47.449955+00:00
-- url     : https://prove2.me/submissions/5be31583-1c5c-492c-9eca-ed56276666bb

module
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed
theorem _root_.solution {X Y : C} {S S' : Subobject X} (h : S ≤ S')
    (p : X ⟶ Y) : imageSubobject (S.arrow ≫ p) ≤ imageSubobject (S'.arrow ≫ p) := by
  rw [← Subobject.ofLE_arrow h, Category.assoc]
  exact imageSubobject_comp_le _ _
end PretorsionImageClosed
