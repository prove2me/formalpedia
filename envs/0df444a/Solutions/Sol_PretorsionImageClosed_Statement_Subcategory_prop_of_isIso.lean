-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.prop_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:20:43.500354+00:00
-- url     : https://prove2.me/submissions/1928886e-cf23-468b-bdab-d70cd09448f0

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
theorem _root_.solution {X Y : C} (f : X ⟶ Y) [IsIso f] (hX : Z.prop X) : Z.prop Y :=
  Z.prop_of_iso (asIso f) hX
end PretorsionImageClosed.Statement.Subcategory
