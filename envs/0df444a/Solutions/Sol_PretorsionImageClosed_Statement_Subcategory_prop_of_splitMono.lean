-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.prop_of_splitMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:47:09.749065+00:00
-- url     : https://prove2.me/submissions/7df21edc-05a7-4b9a-81e5-223b59cf41c2

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
theorem _root_.solution {X Y : C} (f : X ⟶ Y) [IsSplitMono f] (hY : Z.prop Y) : Z.prop X :=
  Z.prop_of_retract ⟨f, retraction f, IsSplitMono.id f⟩ hY
end PretorsionImageClosed.Statement.Subcategory
