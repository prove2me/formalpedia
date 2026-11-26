-- Prove2me | solution 1 for QuadraticFloor.root_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:24.198207+00:00
-- url     : https://prove2.me/submissions/c731f957-f7b9-4459-bb73-059bfb07c259

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_root_count__8bce20a9a3c2


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) {A B : ℤ} (C : ℤ) (hAB : Even (A + B)) (hpA : ¬ (p : ℤ) ∣ A) :
    floorSum A B C p = (C.negOnePow : ℤ) *
      (1 + 2 * ∑ j ∈ range ((p + 1) / 2), legendreSym p (B ^ 2 - 4 * A * C + 8 * A * j)) :=
  root_count' hp2 C hAB hpA
end QuadraticFloor
