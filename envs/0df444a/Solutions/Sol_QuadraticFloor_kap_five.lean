-- Prove2me | solution 1 for QuadraticFloor.kap_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:18.1645+00:00
-- url     : https://prove2.me/submissions/14add0e2-57bf-40ae-b18e-d44cb162fe78

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (p : ℕ) : kap p 5 = -1 := by unfold kap; split_ifs <;> decide
end QuadraticFloor
