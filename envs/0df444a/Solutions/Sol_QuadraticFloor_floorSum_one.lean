-- Prove2me | solution 1 for QuadraticFloor.floorSum_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:06:36.852696+00:00
-- url     : https://prove2.me/submissions/12bc99dc-b68f-4f23-8cb5-3582fc024f3f

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_floorSum_one__50c18f664e37


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) :
    (floorSum 1 1 0 p : ℂ) = 1 - bern (8 * p) (fun x => (eta p x : ℂ)) :=
  floorSum_one' hp2
end QuadraticFloor
