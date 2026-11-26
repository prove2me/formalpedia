-- Prove2me | solution 1 for QuadraticFloor.negOnePow_ediv_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:32.768997+00:00
-- url     : https://prove2.me/submissions/0e55d80c-c864-4d6b-be59-ecd340e8bd61

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace QuadraticFloor
theorem _root_.solution (v : ℤ) (k : ℤ) (hp0 : (p : ℤ) ≠ 0) :
    (((v + p * k) / (p : ℤ)).negOnePow : ℤ) = ((v / p).negOnePow : ℤ) * (k.negOnePow : ℤ) := by
  rw [Int.add_mul_ediv_left _ _ hp0, Int.negOnePow_add, Units.val_mul]
end QuadraticFloor
