-- Prove2me | solution 1 for ReLUBinaryDepth.ProductTradeoff.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:44:46.599768+00:00
-- url     : https://prove2.me/submissions/eab6bf8a-ca02-42f5-bafb-917ac55e4e42

import Mathlib
import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Construction
import Theorems.Thm_ReLUBinaryDepth_ProductTradeoff_lemma_2_2
import Theorems.Thm_ReLUBinaryDepth_ProductTradeoff_lemma_2_3

section
set_option autoImplicit false

namespace ReLUBinaryDepth.ProductTradeoff.Dev.T11

open ReLUBinaryDepth.ProductTradeoff Filter

theorem asym (C : ℝ) (hC : 0 < C) (A : ℝ) (hA : 1 ≤ A) (k : ℕ) (d : ℕ → ℕ)
    (hdo : Asymptotics.IsLittleO atTop (fun n : ℕ => (d n : ℝ)) (fun n : ℕ => (n : ℝ) / Real.log n))
    (hineq : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ n ≤ C * (A * ((n : ℝ) + 1) ^ k) ^ (d n)) : False := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set ε : ℝ := Real.log 2 / (8 * ((k : ℝ) + 2)) with hε
  have hεpos : 0 < ε := by positivity
  have h1 := hdo.def hεpos
  have hN : ∀ᶠ n : ℕ in atTop, (2 : ℕ) ≤ n ∧ A ≤ (n : ℝ) + 1 ∧
      Real.log C < (3 / 4) * Real.log 2 * n := by
    have a1 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
    have a2 : ∀ᶠ n : ℕ in atTop, A ≤ (n : ℝ) + 1 := by
      obtain ⟨N0, hN0⟩ := exists_nat_ge A
      filter_upwards [eventually_ge_atTop N0] with n hn
      have : (N0 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have a3 : ∀ᶠ n : ℕ in atTop, Real.log C < (3 / 4) * Real.log 2 * n := by
      obtain ⟨N0, hN0⟩ := exists_nat_gt (Real.log C / ((3 / 4) * Real.log 2))
      filter_upwards [eventually_ge_atTop N0] with n hn
      have : (N0 : ℝ) ≤ n := by exact_mod_cast hn
      have hpos : 0 < (3 / 4) * Real.log 2 := by positivity
      have := (div_lt_iff₀ hpos).1 (lt_of_lt_of_le hN0 this)
      linarith
    filter_upwards [a1, a2, a3] with n x y z using ⟨x, y, z⟩
  obtain ⟨n, ⟨hn2, hAn, hCn⟩, hdn, hin⟩ := (hN.and (h1.and hineq)).exists
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hn0 : (0 : ℝ) < n := by linarith
  -- log of the inequality
  have hpow : (0 : ℝ) < A * ((n : ℝ) + 1) ^ k := by positivity
  have hlog : (n : ℝ) * Real.log 2 ≤ Real.log C + (d n : ℝ) * (Real.log A + k * Real.log ((n : ℝ) + 1)) := by
    have hpos : (0 : ℝ) < C * (A * ((n : ℝ) + 1) ^ k) ^ (d n) := by positivity
    have := Real.log_le_log (by positivity) hin
    rw [Real.log_mul hC.ne' (by positivity), Real.log_pow, Real.log_pow, Real.log_mul (by linarith) (by positivity),
      Real.log_pow] at this
    push_cast at this
    linarith
  have hA1 : Real.log A ≤ 2 * Real.log n := by
    calc Real.log A ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) hAn
      _ ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
  have hA2 : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log n := by
    calc Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
  have hsum : Real.log A + k * Real.log ((n : ℝ) + 1) ≤ 2 * ((k : ℝ) + 1) * Real.log n := by
    have : (k : ℝ) * Real.log ((n : ℝ) + 1) ≤ k * (2 * Real.log n) :=
      mul_le_mul_of_nonneg_left hA2 (Nat.cast_nonneg k)
    nlinarith
  have hsum0 : 0 ≤ Real.log A + k * Real.log ((n : ℝ) + 1) := by
    have : 0 ≤ Real.log A := Real.log_nonneg hA
    have : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
    positivity
  have hdn' : (d n : ℝ) ≤ ε * ((n : ℝ) / Real.log n) := by
    have := hdn
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)] at this
    exact this
  have hprod : (d n : ℝ) * (Real.log A + k * Real.log ((n : ℝ) + 1)) ≤
      ε * ((n : ℝ) / Real.log n) * (2 * ((k : ℝ) + 1) * Real.log n) :=
    mul_le_mul hdn' hsum hsum0 (by positivity)
  have heq : ε * ((n : ℝ) / Real.log n) * (2 * ((k : ℝ) + 1) * Real.log n) =
      2 * ε * ((k : ℝ) + 1) * n := by
    field_simp
  have hε2 : 2 * ε * ((k : ℝ) + 1) ≤ Real.log 2 / 4 := by
    rw [hε, show 2 * (Real.log 2 / (8 * ((k : ℝ) + 2))) * ((k : ℝ) + 1) =
      Real.log 2 / 4 * (((k : ℝ) + 1) / ((k : ℝ) + 2)) by field_simp; ring]
    have : ((k : ℝ) + 1) / ((k : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  have : 2 * ε * ((k : ℝ) + 1) * n ≤ Real.log 2 / 4 * n :=
    mul_le_mul_of_nonneg_right hε2 hn0.le
  nlinarith

end ReLUBinaryDepth.ProductTradeoff.Dev.T11

namespace ReLUBinaryDepth.ProductTradeoff

open ReLUBinaryDepth.ProductTradeoff.Dev.T11 in
theorem chk_theorem_1_1 :
    (∀ (n : ℕ) (B : ℝ) (θ : Fin n → Bool → ℝ), Admissible B θ →
      ∃ N : Network n, N.depth = n + 1 ∧ N.width ≤ 2 ∧
        N.outputRelu = true ∧ N.Computes (productMap θ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (B : ℝ) (θ : Fin n → Bool → ℝ),
      Admissible B θ → LinearIndependent ℚ (productMap θ) →
      ∀ (N : Network n) (w : ℕ), n ≤ w → N.width ≤ w →
        N.Computes (productMap θ) → (2 : ℝ) ^ n ≤ C * (w : ℝ) ^ N.depth) ∧
    (∀ (B : ℕ → ℝ) (θ : (n : ℕ) → Fin n → Bool → ℝ)
        (N : (n : ℕ) → Network n),
      (∀ᶠ n in Filter.atTop,
        Admissible (B n) (θ n) ∧ LinearIndependent ℚ (productMap (θ n)) ∧
          (N n).Computes (productMap (θ n))) →
      Asymptotics.IsLittleO Filter.atTop
        (fun n : ℕ => ((N n).depth : ℝ))
        (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) →
      ¬ ∃ A : ℝ, 0 < A ∧ ∃ k : ℕ,
        ∀ᶠ n in Filter.atTop, ((N n).width : ℝ) ≤ A * ((n : ℝ) + 1) ^ k) := by
  obtain ⟨C, hC, hCb⟩ := ReLUBinaryDepth.ProductTradeoff.lemma_2_3
  have part2 : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (B : ℝ) (θ : Fin n → Bool → ℝ),
      Admissible B θ → LinearIndependent ℚ (productMap θ) →
      ∀ (N : Network n) (w : ℕ), n ≤ w → N.width ≤ w →
        N.Computes (productMap θ) → (2 : ℝ) ^ n ≤ C * (w : ℝ) ^ N.depth := by
    refine ⟨C, hC, fun n B θ _ hli N w hnw hw hcomp => ?_⟩
    have := hCb n w N (productMap θ) hnw hw hcomp
    have hr : Module.finrank ℚ (outputSpan (productMap θ)) = 2 ^ n := by
      unfold outputSpan
      rw [finrank_span_eq_card hli]
      simp
    rw [hr] at this
    exact_mod_cast this
  refine ⟨?_, part2, ?_⟩
  · intro n B θ hθ
    obtain ⟨a, b, c, d, _⟩ := ReLUBinaryDepth.ProductTradeoff.lemma_2_2 n B θ hθ
    exact ⟨productNetwork B θ, a, b, c, d⟩
  · intro B θ N hev hlo
    rintro ⟨A, hA, k, hk⟩
    obtain ⟨C', hC', h2⟩ := part2
    refine asym C' hC' (A + 1) (by linarith) (k + 1) (fun n => (N n).depth) hlo ?_
    filter_upwards [hev, hk] with n hn hwn
    obtain ⟨hadm, hli, hcomp⟩ := hn
    have h := h2 n (B n) (θ n) hadm hli (N n) (max n (N n).width) (le_max_left _ _)
      (le_max_right _ _) hcomp
    have hn1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (k + 1) :=
      one_le_pow₀ (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hp : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ (k + 1) := by
      calc (n : ℝ) + 1 = ((n : ℝ) + 1) ^ 1 := by ring
        _ ≤ ((n : ℝ) + 1) ^ (k + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    have hpk : ((n : ℝ) + 1) ^ k ≤ ((n : ℝ) + 1) ^ (k + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hw : (((max n (N n).width : ℕ)) : ℝ) ≤ (A + 1) * ((n : ℝ) + 1) ^ (k + 1) := by
      rw [Nat.cast_max]
      apply max_le
      · nlinarith
      · calc ((N n).width : ℝ) ≤ A * ((n : ℝ) + 1) ^ k := hwn
          _ ≤ A * ((n : ℝ) + 1) ^ (k + 1) := mul_le_mul_of_nonneg_left hpk hA.le
          _ ≤ (A + 1) * ((n : ℝ) + 1) ^ (k + 1) := by nlinarith
    calc (2 : ℝ) ^ n ≤ C' * (((max n (N n).width : ℕ)) : ℝ) ^ (N n).depth := h
      _ ≤ C' * ((A + 1) * ((n : ℝ) + 1) ^ (k + 1)) ^ (N n).depth :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hw _) hC'.le

end ReLUBinaryDepth.ProductTradeoff
end

theorem solution : type_of% @ReLUBinaryDepth.ProductTradeoff.chk_theorem_1_1 := @ReLUBinaryDepth.ProductTradeoff.chk_theorem_1_1
