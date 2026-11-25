-- Prove2me | solution 1 for PretorsionImageClosed.Statement.upperFirst_prop_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:56:49.408815+00:00
-- url     : https://prove2.me/submissions/078ac2e4-a0ec-460e-b683-b1d59144b44a

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
open Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable (Z : Subcategory C) (hZ : Z.IsImageClosed)
namespace PretorsionImageClosed.Statement
theorem _root_.solution (X : C) :
    (upperFirst Z hZ).prop X ↔ ∀ (N : C) (f : X ⟶ N), Z.prop N → Z.prop (imageSubobject f : C) :=
  Iff.rfl
end PretorsionImageClosed.Statement
