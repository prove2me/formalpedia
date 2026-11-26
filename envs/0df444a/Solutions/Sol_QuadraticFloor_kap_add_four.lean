-- Prove2me | solution 1 for QuadraticFloor.kap_add_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:05.604394+00:00
-- url     : https://prove2.me/submissions/9bca1945-579c-4a1d-af67-4aea303f5dcc

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (p : ℕ) (y : ZMod 8) : kap p (y + 4) = -kap p y := by
  unfold kap
  split_ifs
  · revert y; decide
  · revert y; decide
end QuadraticFloor
