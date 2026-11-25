-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isTrivial_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:27:01.143597+00:00
-- url     : https://prove2.me/submissions/a28dff3a-9a29-4b51-bea5-8f155dad22a1

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject

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
variable (T F : Subcategory C) (X : C)
variable {T F X}
namespace PretorsionImageClosed.Statement
theorem _root_.solution (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed) {X Y : C}
    (f : X ⟶ Y) (hX : T.prop X) (hY : F.prop Y) : IsTrivial (T.prop ⊓ F.prop) f :=
  ⟨_, ⟨T.prop_of_iso (imageSubobjectIso f).symm (hT (factorThruImage f) inferInstance hX),
    hF (imageSubobject f).arrow inferInstance hY⟩, factorThruImageSubobject f,
    (imageSubobject f).arrow, imageSubobject_arrow_comp f⟩
end PretorsionImageClosed.Statement
