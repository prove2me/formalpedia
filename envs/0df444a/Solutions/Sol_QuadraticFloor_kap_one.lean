-- Prove2me | solution 1 for QuadraticFloor.kap_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:17.563248+00:00
-- url     : https://prove2.me/submissions/f33e04ed-91ff-42b7-9907-059a8f32b3e4

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (p : ℕ) : kap p 1 = 1 := by unfold kap; split_ifs <;> decide
end QuadraticFloor
