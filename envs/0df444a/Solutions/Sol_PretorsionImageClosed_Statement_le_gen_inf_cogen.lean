-- Prove2me | solution 1 for PretorsionImageClosed.Statement.le_gen_inf_cogen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:53:19.857595+00:00
-- url     : https://prove2.me/submissions/c132975f-f02b-4f1f-9439-84f41ecc1d78

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable (Z : Subcategory C) (hZ : Z.IsImageClosed)
variable {Z}
variable (Z)
namespace PretorsionImageClosed.Statement
theorem _root_.solution : Z.prop ≤ Gen Z ⊓ Cogen Z := fun X hX => ⟨le_gen Z X hX, le_cogen Z X hX⟩
end PretorsionImageClosed.Statement
