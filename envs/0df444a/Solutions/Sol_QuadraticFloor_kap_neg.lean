-- Prove2me | solution 1 for QuadraticFloor.kap_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:18.913354+00:00
-- url     : https://prove2.me/submissions/b08b1045-7e30-416d-8297-dee22289e30b

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (p : ℕ) (y : ZMod 8) : kap p (-y) = kap p (-1) * kap p y := by
  rw [← map_mul, neg_one_mul]
end QuadraticFloor
