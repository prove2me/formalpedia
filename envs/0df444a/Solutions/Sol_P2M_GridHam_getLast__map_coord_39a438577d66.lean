-- Prove2me | solution 1 for P2M_GridHam_getLast__map_coord_39a438577d66
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:29:29.605086+00:00
-- url     : https://prove2.me/submissions/a31dc5e7-c0d4-4690-beac-c400d04edfff

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (f : Coord → Coord) : ∀ (l : List Coord) (t : Coord),
    l.getLast? = some t → (l.map f).getLast? = some (f t) := by
  intro l
  induction l with
  | nil => intro t h; simp at h
  | cons a l ih =>
    intro t h
    cases l with
    | nil =>
      have hat : a = t := by simpa using h
      rw [← hat]
      rfl
    | cons b rest =>
      have e1 : (a :: b :: rest).getLast? = (b :: rest).getLast? := rfl
      have e2 : ((a :: b :: rest).map f).getLast? = ((b :: rest).map f).getLast? := rfl
      rw [e1] at h
      rw [e2]
      exact ih t h
end GridHam
