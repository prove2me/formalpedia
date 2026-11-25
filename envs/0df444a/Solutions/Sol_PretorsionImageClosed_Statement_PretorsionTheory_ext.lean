-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:39:14.006445+00:00
-- url     : https://prove2.me/submissions/2cb83bc9-580b-414c-8ba6-bd6fb062b7c6

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
variable {C : Type*} [Category C] {Z : ObjectProperty C}
namespace PretorsionImageClosed.Statement
namespace PretorsionTheory
theorem _root_.solution {D : Type*} [Category D] [HasZeroMorphisms D] [HasBinaryBiproducts D]
    {P Q : PretorsionTheory D} (hT : P.T = Q.T) (hF : P.F = Q.F) : P = Q := by
  cases P
  cases Q
  cases hT
  cases hF
  rfl
end PretorsionTheory
end PretorsionImageClosed.Statement
