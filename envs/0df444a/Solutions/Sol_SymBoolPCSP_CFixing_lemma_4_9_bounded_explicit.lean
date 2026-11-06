-- Prove2me | solution 1 for SymBoolPCSP.CFixing.lemma_4_9_bounded_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-05T20:18:15.553041+00:00
-- url     : https://prove2.me/submissions/9a6852e2-4de9-40ea-83a6-acb8803d8b60

import Mathlib
import Theorems.Thm_AddClosure_mem_of_add_closed_pair
import Theorems.Thm_SymBoolPCSP_CFixing_sum_conditions_add_closed

namespace SymBoolPCSP.CFixing

/-- Bounded form of Lemma 4.9 of Brakensiek–Guruswami, with the explicit constant `c(n) = 0` for `n = 1` and
`c(n) = 1 + (2n-2)(3n-4)` for `n ≥ 2`. -/
theorem lemma_4_9_bounded_explicit (n N : ℕ) (hn : 0 < n) (S₀ S₁ : Set ℕ)
    (h0 : 0 ∈ S₀) (h1 : 1 ∈ S₁)
    (hs0 : ∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀)
    (hs1 : ∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
      a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) :
    (Odd n → (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ≤ N →
      (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ∈ S₀ ∧
      (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ∈ S₁) ∧
    (Even n → ∀ M : ℕ, (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ≤ M → M ≤ N →
      (Even M → M ∈ S₀) ∧ (Odd M → M ∈ S₁)) := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · -- n = 1
    have hn1 : n = 1 := by omega
    subst hn1
    refine ⟨fun _ _ => ⟨by simpa using h0, ?_⟩, fun he => absurd he (by decide)⟩
    have := hs1 0 h0 (fun i => absurd i.2 (by simp)) (fun i => absurd i.2 (by simp))
      (by simp <;> omega)
    simpa using this
  · have hne : n ≠ 1 := by omega
    simp only [hne, if_false]
    obtain ⟨c0p, c0q, c1p, c1q⟩ := sum_conditions_add_closed n N hge S₀ S₁ h0 h1 hs0 hs1
    have hp : 0 < 2 * n - 2 := by omega
    -- gcd(2n-2, 3n-4) divides 2
    have hg2 : Nat.gcd (2 * n - 2) (3 * n - 4) ∣ 2 := by
      have h3 : Nat.gcd (2 * n - 2) (3 * n - 4) ∣ 3 * (2 * n - 2) :=
        Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 3
      have h4 : Nat.gcd (2 * n - 2) (3 * n - 4) ∣ 2 * (3 * n - 4) :=
        Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 2
      have := Nat.dvd_sub h3 h4
      have e : 3 * (2 * n - 2) - 2 * (3 * n - 4) = 2 := by omega
      rwa [e] at this
    refine ⟨fun hodd hN => ?_, fun heven M hM hMN => ?_⟩
    · have hg1 : Nat.gcd (2 * n - 2) (3 * n - 4) = 1 := by
        have hoddq : Odd (3 * n - 4) := by
          obtain ⟨k, hk⟩ := hodd; exact ⟨3 * k - 1, by omega⟩
        have hd := Nat.le_of_dvd (by norm_num) hg2
        have hgo : ¬ 2 ∣ Nat.gcd (2 * n - 2) (3 * n - 4) := fun h2 =>
          (Nat.not_even_iff_odd.mpr hoddq) (even_iff_two_dvd.mpr (h2.trans (Nat.gcd_dvd_right _ _)))
        have hpos := Nat.gcd_pos_of_pos_left (3 * n - 4) hp
        interval_cases h : Nat.gcd (2 * n - 2) (3 * n - 4)
        · rfl
        · exact absurd (dvd_refl 2) hgo
      constructor
      · exact AddClosure.mem_of_add_closed_pair hp h0 c0p c0q (by omega) hN (by rw [hg1]; exact one_dvd _)
      · exact AddClosure.mem_of_add_closed_pair hp h1 c1p c1q (by omega) hN (by rw [hg1]; exact one_dvd _)
    · have hg : Nat.gcd (2 * n - 2) (3 * n - 4) = 2 := by
        have h2g : 2 ∣ Nat.gcd (2 * n - 2) (3 * n - 4) := by
          obtain ⟨k, hk⟩ := heven
          exact Nat.dvd_gcd ⟨n - 1, by omega⟩ ⟨3 * k - 2, by omega⟩
        exact Nat.dvd_antisymm hg2 h2g
      constructor
      · intro hMe
        refine AddClosure.mem_of_add_closed_pair hp h0 c0p c0q (by omega) hMN ?_
        rw [hg, Nat.sub_zero]; exact even_iff_two_dvd.mp hMe
      · intro hMo
        refine AddClosure.mem_of_add_closed_pair hp h1 c1p c1q (by omega) hMN ?_
        rw [hg]; obtain ⟨k, hk⟩ := hMo; exact ⟨k, by omega⟩

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution (n N : ℕ) (hn : 0 < n) (S₀ S₁ : Set ℕ)
    (h0 : 0 ∈ S₀) (h1 : 1 ∈ S₁)
    (hs0 : ∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀)
    (hs1 : ∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
      a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) :
    (Odd n → (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ≤ N →
      (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ∈ S₀ ∧
      (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ∈ S₁) ∧
    (Even n → ∀ M : ℕ, (if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)) ≤ M → M ≤ N →
      (Even M → M ∈ S₀) ∧ (Odd M → M ∈ S₁)) :=
  SymBoolPCSP.CFixing.lemma_4_9_bounded_explicit n N hn S₀ S₁ h0 h1 hs0 hs1
