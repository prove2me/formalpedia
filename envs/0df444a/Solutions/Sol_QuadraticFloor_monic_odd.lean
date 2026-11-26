-- Prove2me | solution 1 for QuadraticFloor.monic_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:07:15.414532+00:00
-- url     : https://prove2.me/submissions/cd397a0f-d2f5-4570-98eb-fb19f84365a3

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_monic_odd__8e05b6979b8c


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (t b : ℤ) :
    floorSum 1 (2 * t + 1) b p = (floorSum 1 1 0 p - 1) + ((b - t * (t + 1)).negOnePow : ℤ) -
      2 * osum (b - t * (t + 1)) (fun j => (j.negOnePow : ℤ) * legendreSym p (-4 * j - 3)) :=
  monic_odd' hp2 t b
end QuadraticFloor
