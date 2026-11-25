-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.prop_cokernel_top_arrow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:16:53.151896+00:00
-- url     : https://prove2.me/submissions/5fe3fce2-9165-4915-9da1-3da2bb4bb283

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalTraceReject

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Subcategory
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (Z : Subcategory (Statement.LinRep k n)) (X : Statement.LinRep k n) :
    Z.prop (cokernel (⊤ : Subobject X).arrow) :=
  Z.prop_of_isZero ((isZero_zero _).of_iso (cokernel.ofEpi _))
end PretorsionImageClosed.LinearQuiver
