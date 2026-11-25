-- Prove2me | solution 1 for PretorsionImageClosed.Statement.greatestRealization_middle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:06:07.296737+00:00
-- url     : https://prove2.me/submissions/501512d8-a75b-4836-bbd1-6477ef08ba75

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
theorem _root_.solution : (greatestRealization Z hZ).middle = Z.prop :=
  upperFirst_inf_lowerSecond Z hZ
end PretorsionImageClosed.Statement
