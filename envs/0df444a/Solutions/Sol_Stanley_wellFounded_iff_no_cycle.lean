-- Prove2me | solution 1 for Stanley.wellFounded_iff_no_cycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:13.849863+00:00
-- url     : https://prove2.me/submissions/79b15b06-bbd9-4663-89fb-e623312959b2

module
public import Definitions.Def_Stanley_Definitions
public import Mathlib.Order.WellFounded
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_Stanley_Orientation

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset
universe u
variable {V : Type u} (G : SimpleGraph V)
namespace Stanley
theorem _root_.solution [Finite V] (r : V → V → Prop) :
    WellFounded r ↔ ∀ v, ¬ Relation.TransGen r v v := by
  constructor
  · intro h v
    induction h.transGen.apply v with
    | intro x _ ih => exact fun hx => ih x hx hx
  · intro h
    have : Std.Irrefl (Relation.TransGen r) := ⟨h⟩
    have hwf := Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen r)
    exact Subrelation.wf (fun h => Relation.TransGen.single h) hwf
end Stanley
