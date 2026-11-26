-- Prove2me | solution 1 for QuadraticFloor.quartic_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:07:04.589575+00:00
-- url     : https://prove2.me/submissions/dbf630a6-5882-474d-aa20-b11f93fd3b2c

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_quartic_split__dd2adffe716c


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((floorSum 5 3 0 p - floorSum 5 1 0 p : ℤ) : ℝ) = (bern (40 * p) (Theta p)).re :=
  quartic_split' hp2 hp5
end QuadraticFloor
