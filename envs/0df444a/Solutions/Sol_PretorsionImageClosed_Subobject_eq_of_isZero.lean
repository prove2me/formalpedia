-- Prove2me | solution 1 for PretorsionImageClosed.Subobject.eq_of_isZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:25:06.316787+00:00
-- url     : https://prove2.me/submissions/0e026318-5d06-407d-994f-0980673136ae

module
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed
namespace Subobject
theorem _root_.solution {X : C} (hX : IsZero X) (S S' : Subobject X) : S = S' :=
  le_antisymm (Subobject.le_of_comm 0 (hX.eq_of_tgt _ _)) (Subobject.le_of_comm 0 (hX.eq_of_tgt _ _))
end Subobject
end PretorsionImageClosed
