-- Prove2me | solution 1 for QuadraticFloor.monic_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:07:16.092872+00:00
-- url     : https://prove2.me/submissions/b2310da3-d7e4-44a2-9224-2200ee77e230

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_monic_even__b68b70dddb0d


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (t b : ℤ) :
    floorSum 1 (2 * t) b p = (((b - t ^ 2) / (p : ℤ)).negOnePow : ℤ) -
      2 * osum t (fun m => (((m ^ 2 + (b - t ^ 2)) / (p : ℤ)).negOnePow : ℤ)) :=
  monic_even' hp2 t b
end QuadraticFloor
