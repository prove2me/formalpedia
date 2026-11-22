-- Prove2me | solution 1 for P2M_GridHam_head__append_of_head_13b1b2448961
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:27:55.384026+00:00
-- url     : https://prove2.me/submissions/6d46b85a-9c0f-40a6-8231-d39b7228da00

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (l M : List Coord) (x : Coord) (h : l.head? = some x) :
    (l ++ M).head? = some x := by
  cases l with
  | nil => simp at h
  | cons z r => simpa using h
end GridHam
