-- Prove2me | solution 1 for P2M_GridHam_head__map_of_95c870c06cfa
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:40:15.250738+00:00
-- url     : https://prove2.me/submissions/982cd963-88bf-4b09-adc3-8ce30e98e9e2

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (f : Coord → Coord) (l : List Coord) (x : Coord)
    (h : l.head? = some x) : (l.map f).head? = some (f x) := by
  cases l with
  | nil => simp at h
  | cons y l =>
    have hyx : y = x := by simpa using h
    subst hyx
    rfl
end GridHam
