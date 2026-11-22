-- Prove2me | solution 1 for P2M_GridHam_mem_of_getLast__beac85f634f6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:42:55.415641+00:00
-- url     : https://prove2.me/submissions/86e01a43-9f74-4997-a62b-24cb9a1125fe

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution : ∀ (l : List Coord) (t : Coord), l.getLast? = some t → t ∈ l := by
  intro l
  induction l with
  | nil => intro t h; simp at h
  | cons a l ih =>
    intro t h
    cases l with
    | nil =>
      have hat : a = t := by simpa using h
      rw [← hat]
      simp
    | cons b rest =>
      have e1 : (a :: b :: rest).getLast? = (b :: rest).getLast? := rfl
      rw [e1] at h
      exact List.mem_cons.mpr (Or.inr (ih t h))
end GridHam
