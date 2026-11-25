-- Prove2me | solution 1 for PretorsionImageClosed.Statement.finInf_prop_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:36:34.352811+00:00
-- url     : https://prove2.me/submissions/afe95d81-475d-4d18-aa20-0921765398ef

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable {ι : Type*} (F : ι → Subcategory C)
namespace PretorsionImageClosed.Statement
theorem _root_.solution (J : Finset ι) (X : C) : (finInf F J).prop X ↔ ∀ i ∈ J, (F i).prop X := by
  rw [finInf, iInf_prop_iff]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i.1 i.2⟩
end PretorsionImageClosed.Statement
