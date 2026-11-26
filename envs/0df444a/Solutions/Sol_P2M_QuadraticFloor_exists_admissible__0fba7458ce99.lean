-- Prove2me | solution 1 for P2M_QuadraticFloor_exists_admissible__0fba7458ce99
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:52.009491+00:00
-- url     : https://prove2.me/submissions/971770d0-50b3-4055-92a8-515ae9ffd1b7

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution {A : ℕ} (hA : Odd A) {B₀ : ℤ} (hB₀ : Int.gcd B₀ A = 1) :
    ∃ B C : ℤ, Admissible A B C ∧ B ≡ B₀ [ZMOD A] := by
  have hAz : Odd (A : ℤ) := by exact_mod_cast hA
  have hApos : (0 : ℤ) < A := by exact_mod_cast hA.pos
  obtain ⟨B, hBodd, hBmod, hBgcd⟩ : ∃ B : ℤ, Odd B ∧ B ≡ B₀ [ZMOD A] ∧ Int.gcd B A = 1 := by
    rcases Int.even_or_odd B₀ with hB | hB
    · refine ⟨B₀ + A, hB.add_odd hAz, ?_, ?_⟩
      · show (B₀ + A) % A = B₀ % A
        simp
      · rw [← Int.isCoprime_iff_gcd_eq_one] at hB₀ ⊢
        simpa using hB₀.add_mul_left_left 1
    · exact ⟨B₀, hB, rfl, hB₀⟩
  refine ⟨B, (B ^ 2 - 1) / (4 * A), ⟨hBodd, hBgcd, ?_, ?_⟩, hBmod⟩
  · have h1 := Int.emod_add_mul_ediv (B ^ 2 - 1) (4 * A)
    have h2 := Int.emod_nonneg (B ^ 2 - 1) (show (4 * (A : ℤ)) ≠ 0 by omega)
    linarith
  · have h1 := Int.emod_add_mul_ediv (B ^ 2 - 1) (4 * A)
    have h3 := Int.emod_lt_of_pos (B ^ 2 - 1) (show (0 : ℤ) < 4 * A by omega)
    rcases lt_or_eq_of_le (show B ^ 2 - 4 * A * ((B ^ 2 - 1) / (4 * A)) ≤ 4 * A by linarith)
      with hlt | heq
    · exact hlt
    · exfalso
      have hB2 : Odd (B ^ 2) := hBodd.pow
      have : Even (B ^ 2) := ⟨2 * A * ((B ^ 2 - 1) / (4 * A) + 1), by linarith⟩
      exact (Int.not_even_iff_odd.2 hB2) this
end QuadraticFloor
