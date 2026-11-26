-- Prove2me | solution 1 for QuadraticFloor.admissible_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:46:10.817667+00:00
-- url     : https://prove2.me/submissions/169a91a9-c7ae-4bdb-95d3-9a43cdbc71c9

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
theorem _root_.solution {A : ℕ} (hA : Odd A) {B C : ℤ} (hBC : Admissible A B C) :
    ∃ d : ℕ, (d : ℤ) = B ^ 2 - 4 * A * C ∧ 1 ≤ d ∧ d < 4 * A ∧ d % 4 = 1 ∧
      (d % 8 = if Even C then 1 else 5) := by
  obtain ⟨hB, -, hD1, hD2⟩ := hBC
  refine ⟨(B ^ 2 - 4 * A * C).toNat, Int.toNat_of_nonneg (by omega), by omega, by omega, ?_⟩
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨t, ht⟩ := Int.even_mul_succ_self b
  obtain ⟨a, ha⟩ := hA
  have hA' : (A : ℤ) = 2 * a + 1 := by exact_mod_cast ha
  have key : (2 * b + 1) ^ 2 - 4 * (A : ℤ) * C = 1 + 8 * (t - a * C) - 4 * C := by
    rw [hA']; linear_combination 4 * ht
  have hnn : 0 ≤ (2 * b + 1) ^ 2 - 4 * (A : ℤ) * C := by omega
  have hcast : (((2 * b + 1) ^ 2 - 4 * (A : ℤ) * C).toNat : ℤ) =
      1 + 8 * (t - a * C) - 4 * C := by rw [Int.toNat_of_nonneg hnn, key]
  generalize ((2 * b + 1) ^ 2 - 4 * (A : ℤ) * C).toNat = d at hcast ⊢
  generalize t - a * C = w at hcast
  rcases Int.even_or_odd C with ⟨c, hc⟩ | ⟨c, hc⟩
  · have : Even C := ⟨c, hc⟩
    simp only [this, ite_true]
    omega
  · have : ¬ Even C := Int.not_even_iff_odd.2 ⟨c, hc⟩
    simp only [this, ite_false]
    omega
end QuadraticFloor
