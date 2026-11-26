-- Prove2me | solution 1 for P2M_QuadraticFloor_window_form__e277282c21f6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:51.85887+00:00
-- url     : https://prove2.me/submissions/3fb029f5-05a7-40e7-bc88-384a1ecd1948

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
public import Theorems.Thm_QuadraticFloor_admissible_data
public import Theorems.Thm_P2M_QuadraticFloor_window__8c99d9986259

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
        eta p x := by
  obtain ⟨d, hdD, -, hd4A, -, hd8⟩ := admissible_data hA hBC
  have : (B ^ 2 - 4 * A * C).toNat = d := by omega
  rw [this]
  exact window' hp2 hA hpA hBC hdD hd4A hd8
end QuadraticFloor
