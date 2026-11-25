-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.isCompletelyJoinIrreducible_of_greatest_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:26:24.899388+00:00
-- url     : https://prove2.me/submissions/79d1e7f4-ad39-470f-8068-65841b7da670

module
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_ClosedSets
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed
open PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    {L : Type*} [CompleteLattice L] {j jₛ : L}
    (hₛ : jₛ < j) (hgreatest : ∀ ⦃a : L⦄, a < j → a ≤ jₛ) :
    IsCompletelyJoinIrreducible j := by
  intro S hS
  by_contra hjS
  have hle : sSup S ≤ jₛ := by
    apply sSup_le
    intro a haS
    have haj : a ≤ j := by
      rw [← hS]
      exact le_sSup haS
    have hane : a ≠ j := by
      intro haj'
      exact hjS (haj' ▸ haS)
    exact hgreatest (lt_of_le_of_ne haj hane)
  have hjle : j ≤ jₛ := hS ▸ hle
  exact (not_le_of_gt hₛ) hjle
end PretorsionImageClosed.SetClosure
