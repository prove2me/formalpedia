-- Prove2me | solution 1 for P2M_GridHam_getLast__map_of_0a3c51641c72
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:19:09.391373+00:00
-- url     : https://prove2.me/submissions/db449b32-3c89-4d5b-922a-e462df764b31

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (f : Coord → ℕ) : ∀ (l : List Coord) (t : Coord),
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
