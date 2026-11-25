-- Prove2me | solution 1 for P2M_PretorsionImageClosed_Statement_Subcategory_ext_iff__5d322945f46b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:46:26.386741+00:00
-- url     : https://prove2.me/submissions/2f313e57-9897-4a38-8b38-e21237ab1691

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (Z : Subcategory C)
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution {Z Z' : Subcategory C} : Z = Z' ↔ ∀ X, Z.prop X ↔ Z'.prop X :=
  ⟨fun h X => by rw [h], fun h => ext (funext fun X => propext (h X))⟩
end PretorsionImageClosed.Statement.Subcategory
