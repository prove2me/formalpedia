-- Prove2me | solution 1 for QuadraticFloor.quadratic_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:06:51.838337+00:00
-- url     : https://prove2.me/submissions/ec5aaea6-971b-43ef-a016-c306087f2365

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_quadratic_half__fa71830266b8


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((floorSum 5 1 0 p + floorSum 5 3 0 p - 2 : ℤ) : ℂ) = -(1 / 2) *
      (bern (40 * p) (fun x => (eta p x : ℂ) * (if 5 ∣ x then 0 else 1)) +
        bern (40 * p) (fun x => (eta p x : ℂ) * (jacobiSym x 5 : ℂ))) :=
  quadratic_half' hp2 hp5
end QuadraticFloor
