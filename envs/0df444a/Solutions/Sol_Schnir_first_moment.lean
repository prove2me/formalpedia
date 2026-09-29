-- Prove2me | solution 1 for Schnir.first_moment
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T22:52:09.758982+00:00
-- url     : https://prove2.me/submissions/fa02ba40-223c-4bd7-a8d0-3f6bf35f65a4

import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_Schnir_pi_lower

open Finset Real

namespace Schnir

lemma cheb_log_le_lin (y : ℝ) (hy : 0 < y) : Real.log y ≤ y / 1000 - 1 + 10 * Real.log 2 := by
  have h1 : Real.log y = Real.log (y / 1024) + Real.log 1024 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]; congr 1; field_simp
  have h2 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
  have h3 := Real.log_le_sub_one_of_pos (show 0 < y / 1024 by positivity)
  rw [h1, h2]
  have : y / 1024 ≤ y / 1000 := by
    apply div_le_div_of_nonneg_left hy.le (by norm_num) (by norm_num)
  linarith

lemma cheb_card_odd_primes (M : ℕ) (hM : 2 ≤ M) :
    ((Finset.range (M + 1)).filter (fun p => p.Prime ∧ p ≠ 2)).card + 1 = Nat.primeCounting M := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have : (Finset.range (M + 1)).filter (fun p => p.Prime ∧ p ≠ 2)
      = ((Finset.range (M + 1)).filter Nat.Prime).erase 2 := by
    ext p; simp [Finset.mem_erase]; tauto
  rw [this, Finset.card_erase_add_one]
  simp [Nat.prime_two]; omega

/-- Note eq. (4): first moment, `∑_{s ≤ x} r(s) ≥ x^2 / (9 (log x)^2)` for `x ≥ 2000`. -/
theorem first_moment (x : ℝ) (hx : 2000 ≤ x) :
    x ^ 2 / (9 * (Real.log x) ^ 2) ≤ ∑ s ∈ Finset.range (⌊x⌋₊ + 1), (r s : ℝ) := by
  set N := ⌊x⌋₊
  set M := ⌊x / 2⌋₊
  have hM2 : 2 * M ≤ N := by
    have h1 : ((2 * M : ℕ) : ℝ) ≤ x := by
      push_cast; have := Nat.floor_le (show 0 ≤ x / 2 by linarith); linarith
    exact Nat.le_floor h1
  have hM1000 : 1000 ≤ M := Nat.le_floor (by norm_num; linarith)
  set P := (Finset.range (M + 1)).filter (fun p => p.Prime ∧ p ≠ 2)
  have hcard := cheb_card_odd_primes M (by omega)
  -- combinatorial bound
  have hcomb : (P ×ˢ P).card ≤ ∑ s ∈ Finset.range (N + 1), r s := by
    unfold r
    rw [← Finset.card_sigma]
    apply Finset.card_le_card_of_injOn (fun pq => (⟨pq.1 + pq.2, pq.1⟩ : Σ _ : ℕ, ℕ))
    · intro pq hpq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, P, Finset.mem_filter,
        Finset.mem_range] at hpq
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]
      obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩ := hpq
      refine ⟨by omega, by omega, h2, h3, ?_, ?_⟩
      · rw [Nat.add_sub_cancel_left]; exact h5
      · rw [Nat.add_sub_cancel_left]; exact h6
    · intro a _ b _ hab
      simp only [Sigma.mk.injEq] at hab
      obtain ⟨h1, h2⟩ := hab
      have h2' : a.1 = b.1 := eq_of_heq h2
      ext <;> omega
  rw [Finset.card_product] at hcomb
  have hcombR : ((P.card : ℝ)) ^ 2 ≤ ∑ s ∈ Finset.range (N + 1), (r s : ℝ) := by
    rw [← Nat.cast_sum]; exact_mod_cast (by nlinarith [hcomb] : P.card ^ 2 ≤ _)
  have hPR : (P.card : ℝ) = (Nat.primeCounting M : ℝ) - 1 := by
    rw [← hcard]; push_cast; ring
  have hpl := pi_lower (x / 2) (by linarith)
  rw [← hPR] at hpl
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlx2 : 0 < Real.log (x / 2) := Real.log_pos (by linarith)
  have hle : Real.log (x / 2) ≤ Real.log x := Real.log_le_log (by linarith) (by linarith)
  have hstep : x / (3 * Real.log x) ≤ P.card := by
    refine le_trans ?_ hpl
    rw [show 2 * (x / 2) = x by ring]
    apply div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
  have hpos : 0 ≤ x / (3 * Real.log x) := by positivity
  calc x ^ 2 / (9 * Real.log x ^ 2) = (x / (3 * Real.log x)) ^ 2 := by ring
    _ ≤ (P.card : ℝ) ^ 2 := pow_le_pow_left₀ hpos hstep 2
    _ ≤ _ := hcombR

end Schnir

open Schnir in
theorem solution (x : ℝ) (hx : 2000 ≤ x) :
    x ^ 2 / (9 * (Real.log x) ^ 2) ≤ ∑ s ∈ Finset.range (⌊x⌋₊ + 1), (r s : ℝ) :=
  Schnir.first_moment x hx
