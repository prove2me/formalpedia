-- Prove2me | solution 1 for PretorsionImageClosed.Statement.gen_inf_cogen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:58:30.270255+00:00
-- url     : https://prove2.me/submissions/72f8e672-a053-452e-a2e7-a2070d64499a

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
theorem _root_.solution {D : Subcategory C} (hD : D.IsImageClosed) (hZD : Z ≤ D) :
    Gen Z ⊓ Cogen Z ≤ D.prop := by
  rw [(isImageClosed_iff_eq_gen_inf_cogen D).1 hD]
  rintro X ⟨⟨N, hN, p, hp⟩, ⟨M, hM, i, hi⟩⟩
  exact ⟨⟨N, hZD N hN, p, hp⟩, ⟨M, hZD M hM, i, hi⟩⟩
end PretorsionImageClosed.Statement
