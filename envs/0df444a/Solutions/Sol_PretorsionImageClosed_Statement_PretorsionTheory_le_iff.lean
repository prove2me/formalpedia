-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:36:49.618102+00:00
-- url     : https://prove2.me/submissions/5f5dbaf3-0a05-4a0c-b1b5-579c335cd88f

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed.Statement
namespace PretorsionTheory
theorem _root_.solution {P Q : PretorsionTheory C} : P ≤ Q ↔ P.LE Q := Iff.rfl
end PretorsionTheory
end PretorsionImageClosed.Statement
