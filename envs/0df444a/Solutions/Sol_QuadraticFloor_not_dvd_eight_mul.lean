-- Prove2me | solution 1 for QuadraticFloor.not_dvd_eight_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:20.309427+00:00
-- url     : https://prove2.me/submissions/e1e81a78-9bf5-4422-b904-298b5c277376

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) {A : ℕ} (hpA : ¬ p ∣ A) : ¬ p ∣ 8 * A := by
  intro h
  rcases (Nat.Prime.dvd_mul hp.out).1 h with h8 | h8
  · have : p ∣ 2 ^ 3 := by simpa using h8
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow this))
  · exact hpA h8
end QuadraticFloor
