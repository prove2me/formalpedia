-- Prove2me | solution 1 for P2M_GridHam_getLast__append_cons_527000d4767a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:29:00.913946+00:00
-- url     : https://prove2.me/submissions/dd08f737-a809-4a26-9dfb-121b2736bfcb

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution : ∀ (l1 : List Coord) (c : Coord) (m : List Coord),
    (l1 ++ c :: m).getLast? = (c :: m).getLast? := by
  intro l1
  induction l1 with
  | nil => intro c m; rfl
  | cons x l ih =>
    intro c m
    cases l with
    | nil => rfl
    | cons y l' =>
      have e : ((x :: y :: l') ++ c :: m).getLast? = ((y :: l') ++ c :: m).getLast? := rfl
      rw [e]
      exact ih c m
end GridHam
