-- Prove2me | solution 1 for QuadraticFloor.card_zero_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:24.10047+00:00
-- url     : https://prove2.me/submissions/b6a55bbe-bba9-4cee-a9ce-43c72c1825bf

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (hp5 : p ≠ 5) (B : ℤ) :
    (((range ((p + 1) / 2)).filter fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0).card : ℤ) =
      zB B p := by
  have hzero : ∀ j : ℕ, legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0 ↔ (p : ℤ) ∣ B ^ 2 + 40 * j := by
    intro j; rw [legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h40 : ¬ (p : ℤ) ∣ 40 := by
    intro h
    have h' : p ∣ 2 ^ 3 * 5 := by exact_mod_cast h
    rcases (Nat.Prime.dvd_mul hp.out).1 h' with h2 | h2
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow h2))
    · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).1 h2)
  have huniq : ∀ j₁ ∈ range ((p + 1) / 2), ∀ j₂ ∈ range ((p + 1) / 2),
      (p : ℤ) ∣ B ^ 2 + 40 * j₁ → (p : ℤ) ∣ B ^ 2 + 40 * j₂ → j₁ = j₂ := by
    intro j₁ hj₁ j₂ hj₂ h₁ h₂
    have hd : (p : ℤ) ∣ 40 * ((j₁ : ℤ) - j₂) := by
      have := dvd_sub h₁ h₂; rw [show B ^ 2 + 40 * (j₁ : ℤ) - (B ^ 2 + 40 * j₂) =
        40 * ((j₁ : ℤ) - j₂) by ring] at this; exact this
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.out
    rcases hpr.dvd_or_dvd hd with h | h
    · exact absurd h h40
    · rw [mem_range] at hj₁ hj₂
      have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
      omega
  unfold zB
  split_ifs with hex
  · obtain ⟨j₀, hj₀, hd₀⟩ := hex
    have : (range ((p + 1) / 2)).filter (fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0) = {j₀} := by
      ext j
      simp only [mem_filter, mem_singleton, hzero]
      constructor
      · rintro ⟨hj, hd⟩; exact huniq j hj j₀ hj₀ hd hd₀
      · rintro rfl; exact ⟨hj₀, hd₀⟩
    rw [this, card_singleton]; rfl
  · simp only [not_exists, not_and] at hex
    have : (range ((p + 1) / 2)).filter (fun j : ℕ => legendreSym p (B ^ 2 + 40 * (j : ℤ)) = 0) = ∅ := by
      ext j
      simp only [mem_filter, hzero, Finset.notMem_empty, iff_false, not_and]
      exact hex j
    rw [this, card_empty]; rfl
end QuadraticFloor
