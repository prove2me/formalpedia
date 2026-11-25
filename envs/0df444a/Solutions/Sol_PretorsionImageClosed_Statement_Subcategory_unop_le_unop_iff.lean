-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.unop_le_unop_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:57:22.763388+00:00
-- url     : https://prove2.me/submissions/c9149e16-c3a6-4483-809d-28733532daf2

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
theorem _root_.solution {Z Z' : Subcategory Cᵒᵖ} : Z.unop ≤ Z'.unop ↔ Z ≤ Z' :=
  ⟨fun h X hX => h X.unop hX, fun h X hX => h (Opposite.op X) hX⟩
end Subcategory
end PretorsionImageClosed.Statement
