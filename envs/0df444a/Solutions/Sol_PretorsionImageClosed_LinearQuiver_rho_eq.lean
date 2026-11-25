-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.rho_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:27:51.096725+00:00
-- url     : https://prove2.me/submissions/f54e30f7-02f0-4e7c-963d-743c3df0f0f0

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
variable {m : ℕ} (D : Subcategory (Statement.LinRep k (m + 1)))
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution : rho D.prop = Nat.card (LastPairs D) :=
  Nat.card_congr (lastSkeletonEquiv D)
end PretorsionImageClosed.LinearQuiver
