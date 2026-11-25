-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.prop_interval_of_prop_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:11:14.221716+00:00
-- url     : https://prove2.me/submissions/29a2cb1a-1b1a-46ee-9486-65fa4b892827

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (C : Subcategory (Statement.LinRep k n)) {a c b : Fin n}
    (hac : a ≤ c) (h : C.prop (suffix (k := k) a b c hac : Statement.LinRep k n)) :
    C.prop (interval k c b) :=
  C.prop_of_iso (Subobject.underlyingIso _) h
end PretorsionImageClosed.LinearQuiver
