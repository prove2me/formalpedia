-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isImageClosed_gen_inf_cogen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:56:02.672113+00:00
-- url     : https://prove2.me/submissions/47b51c53-a799-4889-a6ac-45d4507e142b

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
theorem _root_.solution : IsImageClosed (Gen Z ⊓ Cogen Z) := by
  rintro X Y f ⟨⟨N, hN, p, hp⟩, -⟩ ⟨-, ⟨M, hM, i, hi⟩⟩
  exact ⟨⟨N, hN, p ≫ factorThruImage f, epi_comp _ _⟩, ⟨M, hM, image.ι f ≫ i, mono_comp _ _⟩⟩
end PretorsionImageClosed.Statement
