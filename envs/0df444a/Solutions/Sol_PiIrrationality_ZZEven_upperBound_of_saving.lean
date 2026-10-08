-- Prove2me | solution 1 for PiIrrationality.ZZEven.upperBound_of_saving
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T09:48:04.46836+00:00
-- url     : https://prove2.me/submissions/3eddfb7d-e383-41f9-b8f8-23a05606dbac

import Definitions.Def_PiIrrationality_UpperBound
import Definitions.Def_PiIrrationality_ZZEvenForms
import Theorems.Thm_PiIrrationality_ratio_linearForm_upperBound
import Theorems.Thm_PiIrrationality_lcmUpto_le_exp
import Theorems.Thm_PiIrrationality_ZZEven_linearForm
import Theorems.Thm_PiIrrationality_ZZEven_integral_bound
import Theorems.Thm_PiIrrationality_ZZEven_coef_le
import Theorems.Thm_PiIrrationality_ZZEven_coef_ge
import Theorems.Thm_PiIrrationality_ZZEven_phi_lower
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Real

namespace PiIrrationality.ZZEven.Assembly

lemma two_pow_eq_exp (k : ℕ) : (2 : ℝ) ^ k = Real.exp (k * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

lemma M_pos (n : ℕ) : 0 < M n := by
  unfold M
  have h1 : (0 : ℝ) < Nat.lcmUpto (8 * n) := by exact_mod_cast Nat.lcmUpto_pos _
  have h2 : (0 : ℝ) < Phi n := by
    unfold Phi
    exact_mod_cast Finset.prod_pos fun p hp => by
      unfold deletedPrimes at hp
      exact (Finset.mem_filter.mp hp).2.1.pos
  positivity

/-- Eventual upper bound for the normalising multiplier. -/
lemma M_le (δ lam : ℝ) (hδ : 0 < δ)
    (hphi : ∀ᶠ n : ℕ in atTop, Real.exp ((lam - δ) * n) ≤ (Phi n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      M n ≤ 16 * Real.exp ((8 + 9 * δ - lam - 5 * Real.log 2) * n) := by
  have hl : ∀ᶠ n : ℕ in atTop,
      (Nat.lcmUpto (8 * n) : ℝ) ≤ Real.exp ((1 + δ) * ((8 * n : ℕ) : ℝ)) :=
    (tendsto_id.const_mul_atTop' (by norm_num : 0 < 8)).eventually
      (PiIrrationality.lcmUpto_le_exp δ hδ)
  filter_upwards [hl, hphi] with n hl hphi
  unfold M
  have hPhi : 0 < (Phi n : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hphi
  rw [div_le_iff₀ (by positivity), two_pow_eq_exp (5 * n)]
  have hsplit : (1 + δ) * ((8 * n : ℕ) : ℝ) = (8 + 9 * δ - lam - 5 * Real.log 2) * n +
      (((5 * n : ℕ) : ℝ) * Real.log 2 + (lam - δ) * n) := by push_cast; ring
  have h16 : (2 : ℝ) ^ 4 = 16 := by norm_num
  calc (2 : ℝ) ^ 4 * (Nat.lcmUpto (8 * n) : ℝ)
      ≤ 16 * Real.exp ((1 + δ) * ((8 * n : ℕ) : ℝ)) := by
        rw [h16]; exact mul_le_mul_of_nonneg_left hl (by norm_num)
    _ = 16 * Real.exp ((8 + 9 * δ - lam - 5 * Real.log 2) * n) *
          (Real.exp ((5 * n : ℕ) * Real.log 2) * Real.exp ((lam - δ) * n)) := by
        rw [hsplit, Real.exp_add, Real.exp_add]; ring
    _ ≤ 16 * Real.exp ((8 + 9 * δ - lam - 5 * Real.log 2) * n) *
          (Real.exp ((5 * n : ℕ) * Real.log 2) * (Phi n : ℝ)) := by
        gcongr

/-- `c ≤ exp(δ n)` eventually. -/
lemma const_le_exp (c δ : ℝ) (hδ : 0 < δ) : ∀ᶠ n : ℕ in atTop, c ≤ Real.exp (δ * n) := by
  have : Tendsto (fun n : ℕ => Real.exp (δ * n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hδ)
  exact this.eventually_ge_atTop c

end PiIrrationality.ZZEven.Assembly

open PiIrrationality.ZZEven PiIrrationality.ZZEven.Assembly in
theorem solution (K : ℕ) (δ B : ℝ) (hδ : 0 < δ)
    (hs : 0 < 2522 / 100 + 10 * δ - Real.log 2 -
      ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2)))
    (hgap : 0 < 5 * Real.log 2 - 102 / 100 - 11 * δ +
      ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2)))
    (hB₁ : 1 + (2522 / 100 + 10 * δ - Real.log 2 -
        ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2))) /
      (5 * Real.log 2 - 1 - 10 * δ +
        ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2))) ≤ B)
    (hB₂ : 1 + (2522 / 100 + 10 * δ - Real.log 2 -
        ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2))) /
      (5 * Real.log 2 - 102 / 100 - 11 * δ +
        ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2))) ≤ B) :
    PiIrrationality.UpperBound B := by
  set lam : ℝ := ∑ k ∈ Finset.range K, ((4 : ℝ) / (2 * k + 1) - 6 / (3 * k + 2)) with hlam
  set s : ℝ := 2522 / 100 + 10 * δ - Real.log 2 - lam with hsdef
  set t : ℝ := 5 * Real.log 2 - 1 - 10 * δ + lam with htdef
  set g : ℝ := 2420 / 100 + 4 * Real.log 2 - δ with hgdef
  have ht : 0 < t := by rw [htdef]; linarith
  have hsg : s < g := by rw [hsdef, hgdef]; linarith
  have hgs : g - s = 5 * Real.log 2 - 102 / 100 - 11 * δ + lam := by
    rw [hsdef, hgdef]; ring
  -- the linear forms
  have hLF : ∀ n : ℕ, ∃ U V : ℤ, 1 ≤ n →
      (M n : ℂ) * J n = (U : ℂ) + (V : ℂ) * (Real.pi : ℂ) ∧
        (V : ℝ) = -(M n * 16 ^ n * (coef n : ℝ) / 4) := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨U, V, h⟩ := PiIrrationality.ZZEven.linearForm n hn
      exact ⟨U, V, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hn⟩
  choose U V hUV using hLF
  -- |Λ_n| = M_n ‖J_n‖
  have hΛeq : ∀ n, 1 ≤ n → |(U n : ℝ) + V n * Real.pi| = M n * ‖J n‖ := by
    intro n hn
    have h := (hUV n hn).1
    have : ((((U n : ℝ) + V n * Real.pi : ℝ)) : ℂ) = (M n : ℂ) * J n := by
      rw [h]; push_cast; ring
    have habs : |(U n : ℝ) + V n * Real.pi| = ‖((((U n : ℝ) + V n * Real.pi : ℝ)) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [habs, this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (M_pos n)]
  have hVeq : ∀ n, 1 ≤ n → |(V n : ℝ)| = M n * 16 ^ n * (coef n : ℝ) / 4 := by
    intro n hn
    rw [(hUV n hn).2, abs_neg, abs_of_nonneg (by have := M_pos n; positivity)]
  obtain ⟨N₁, hN₁⟩ := PiIrrationality.ZZEven.coef_ge
  have hM := M_le δ lam hδ (PiIrrationality.ZZEven.phi_lower K δ hδ)
  have h16 : ∀ n : ℕ, (16 : ℝ) ^ n = Real.exp (4 * Real.log 2 * n) := by
    intro n
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, two_pow_eq_exp]; push_cast; ring_nf
  apply PiIrrationality.ratio_linearForm_upperBound U V s t g B
    (by rw [hsdef]; linarith) ht hsg hB₁ (by rw [hgs]; exact hB₂)
  · -- coefficient bound
    filter_upwards [hM, eventually_ge_atTop 1, eventually_ge_atTop N₁,
      const_le_exp 4 δ hδ] with n hMn hn hn1 h4
    have hc := hN₁ n hn1
    have hcpos : 0 < (coef n : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hc
    refine ⟨?_, ?_⟩
    · intro h0
      have := hVeq n hn
      rw [h0, Int.cast_zero, abs_zero] at this
      have : 0 < M n * 16 ^ n * (coef n : ℝ) / 4 := by
        have := M_pos n; positivity
      linarith
    · rw [hVeq n hn]
      have hcl := PiIrrationality.ZZEven.coef_le n
      calc M n * 16 ^ n * (coef n : ℝ) / 4
          ≤ 16 * Real.exp ((8 + 9 * δ - lam - 5 * Real.log 2) * n) *
              Real.exp (4 * Real.log 2 * n) * Real.exp (1722 / 100 * n) / 4 := by
            rw [h16]; gcongr
        _ = 4 * Real.exp ((s - δ) * n) := by
            have : (s - δ) * n = (8 + 9 * δ - lam - 5 * Real.log 2) * n +
                4 * Real.log 2 * n + 1722 / 100 * n := by rw [hsdef]; ring
            rw [this, Real.exp_add, Real.exp_add]; ring
        _ ≤ Real.exp (δ * n) * Real.exp ((s - δ) * n) := by gcongr
        _ = Real.exp (s * n) := by rw [← Real.exp_add]; congr 1; ring
  · -- decay of the linear form
    filter_upwards [hM, eventually_ge_atTop 1, const_le_exp 160 δ hδ] with n hMn hn h160
    rw [hΛeq n hn]
    have hJ := PiIrrationality.ZZEven.integral_bound n
    calc M n * ‖J n‖
        ≤ 16 * Real.exp ((8 + 9 * δ - lam - 5 * Real.log 2) * n) *
            (10 * Real.exp (-(7 * (n : ℝ)))) := by
          exact mul_le_mul hMn hJ (norm_nonneg _) (by positivity)
      _ = 160 * Real.exp (-(t + δ) * n) := by
          have : -(t + δ) * n = (8 + 9 * δ - lam - 5 * Real.log 2) * n + -(7 * (n : ℝ)) := by
            rw [htdef]; ring
          rw [this, Real.exp_add]; ring
      _ ≤ Real.exp (δ * n) * Real.exp (-(t + δ) * n) := by gcongr
      _ = Real.exp (-(t * n)) := by rw [← Real.exp_add]; congr 1; ring
  · -- the normalisation-free ratio
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop N₁,
      const_le_exp 40 δ hδ] with n hn hn1 h40
    rw [hΛeq n hn, hVeq n hn]
    have hJ := PiIrrationality.ZZEven.integral_bound n
    have hc := hN₁ n hn1
    have hMp := M_pos n
    have key : ‖J n‖ ≤ Real.exp (-(g * n)) * (16 ^ n * (coef n : ℝ) / 4) := by
      calc ‖J n‖ ≤ 10 * Real.exp (-(7 * (n : ℝ))) := hJ
        _ = 40 * Real.exp (-(g + δ) * n) *
              (Real.exp (4 * Real.log 2 * n) * Real.exp (1720 / 100 * n) / 4) := by
            have : -(7 * (n : ℝ)) = -(g + δ) * n + 4 * Real.log 2 * n + 1720 / 100 * n := by
              rw [hgdef]; ring
            rw [this, Real.exp_add, Real.exp_add]; ring
        _ ≤ Real.exp (δ * n) * Real.exp (-(g + δ) * n) *
              (Real.exp (4 * Real.log 2 * n) * (coef n : ℝ) / 4) := by
            gcongr
        _ = Real.exp (-(g * n)) * (16 ^ n * (coef n : ℝ) / 4) := by
            rw [h16 n]
            have : -(g * n) = δ * n + -(g + δ) * n := by ring
            rw [this, Real.exp_add]
    calc M n * ‖J n‖ ≤ M n * (Real.exp (-(g * n)) * (16 ^ n * (coef n : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left key hMp.le
      _ = Real.exp (-(g * n)) * (M n * 16 ^ n * (coef n : ℝ) / 4) := by ring
