-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.op_prop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:01:36.541223+00:00
-- url     : https://prove2.me/submissions/4c64b803-7cb4-4b84-b09d-216a9a46f4e3

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Opposite
open PretorsionImageClosed.Statement
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed.Statement
namespace Subcategory
theorem _root_.solution (Z : Subcategory C) : Z.op.prop = Z.prop.op := rfl
end Subcategory
end PretorsionImageClosed.Statement
