-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.op_le_op_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:56:18.012367+00:00
-- url     : https://prove2.me/submissions/25c9c576-e4d6-42ab-b296-6b959bc94228

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
theorem _root_.solution {Z Z' : Subcategory C} : Z.op ≤ Z'.op ↔ Z ≤ Z' :=
  ⟨fun h X hX => h (Opposite.op X) hX, fun h X hX => h X.unop hX⟩
end Subcategory
end PretorsionImageClosed.Statement
