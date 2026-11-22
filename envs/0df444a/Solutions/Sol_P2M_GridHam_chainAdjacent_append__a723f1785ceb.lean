-- Prove2me | solution 1 for P2M_GridHam_chainAdjacent_append__a723f1785ceb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:26:31.959005+00:00
-- url     : https://prove2.me/submissions/a712ce74-9103-441f-b663-89c252b20caa

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_chainAdjacent_append

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (l1 M : List Coord) (a b : Coord) (hl : l1.getLast? = some a)
    (h1 : chainAdjacent l1 = true) (hM : M.head? = some b) (hadj : Adjacent a b)
    (h2 : chainAdjacent M = true) : chainAdjacent (l1 ++ M) = true := by
  cases M with
  | nil => simp at hM
  | cons c r =>
    have hcb : c = b := by simpa using hM
    rw [hcb] at h2 ⊢
    exact chainAdjacent_append l1 b r a hl h1 hadj h2
end GridHam
