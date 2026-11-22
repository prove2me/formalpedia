-- Prove2me | solution 1 for P2M_GridHam_nodup_append_right__a582c6ad4e63
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:04:53.796276+00:00
-- url     : https://prove2.me/submissions/193c52ea-7a9a-409f-95a3-64eaabfebf84

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution : ∀ (l1 l2 : List Coord), (l1 ++ l2).Nodup → l2.Nodup := by
  intro l1
  induction l1 with
  | nil => intro l2 h; exact h
  | cons x l ih =>
    intro l2 h
    have h' : (x :: (l ++ l2)).Nodup := h
    exact ih l2 (List.nodup_cons.mp h').2
end GridHam
