-- Prove2me | solution 1 for QuadraticFloor.window_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:30.245732+00:00
-- url     : https://prove2.me/submissions/b4d32e1e-e4a8-4a4b-b4e1-208815322d26

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_window_form__e277282c21f6


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (hpA : ¬ p ∣ A) {B C : ℤ}
    (hBC : Admissible A B C) :
    floorSum A B C p - (C.negOnePow : ℤ) =
      2 * ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = (B ^ 2 - 4 * A * C).toNat),
        eta p x :=
  window_form' hp2 hA hpA hBC
end QuadraticFloor
