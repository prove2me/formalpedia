-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.indCard_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:27:32.970202+00:00
-- url     : https://prove2.me/submissions/fd022584-b536-4c37-a428-9e161ebb6e89

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalSets
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting

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
variable (C : Subcategory (Statement.LinRep k n))
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution : indCard C.prop = Nat.card (IntervalPairs C) :=
  Nat.card_congr (skeletonEquiv C)
end PretorsionImageClosed.LinearQuiver
