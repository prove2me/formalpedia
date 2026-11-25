-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.sInf_T_prop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:49:01.279856+00:00
-- url     : https://prove2.me/submissions/d7a8ad55-7695-44b0-9f94-477fe1e54262

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sInf_eq
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_meetT_prop

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C]
variable [HasLength C]
open PretorsionImageClosed.Statement.PretorsionTheory
namespace PretorsionImageClosed.Statement.PretorsionTheory
theorem _root_.solution (S : Set (PretorsionTheory C)) : (sInf S).T.prop = ⨅ P ∈ S, P.T.prop := by
  rw [sInf_eq]
  exact meetT_prop S
end PretorsionImageClosed.Statement.PretorsionTheory
