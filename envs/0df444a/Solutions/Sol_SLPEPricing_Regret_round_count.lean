-- Prove2me | solution 1 for SLPEPricing.Regret.round_count
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T04:17:14.259428+00:00
-- url     : https://prove2.me/submissions/865081fe-9350-43e7-aae7-4901ab668ca0

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model

open SLPEPricing.Regret

lemma slpe_delta_pow (μ : ℝ) (k : ℕ) : μ * Delta μ (k + 1) = (μ / 2) ^ (2 ^ k) := by
  induction k with
  | zero => simp [Delta]; ring
  | succ k ih =>
    have : Delta μ (k + 2) = μ * Delta μ (k + 1) ^ 2 := rfl
    rw [show k + 1 + 1 = k + 2 by ring, this, pow_succ 2 k, pow_mul, ← ih]
    ring

theorem solution (μ ρ : ℝ) (hμ0 : 0 < μ) (hμ2 : μ < 2) (hρ : 0 < ρ) :
    ∃ C : ℝ, ∀ T : ℕ, 3 ≤ T → (iMax μ ρ T : ℝ) ≤ C + Real.logb 2 (Real.log (T : ℝ)) := by
  set θ := μ / 2 with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by rw [hθ]; linarith
  set L := Real.log (1 / θ) with hL
  have hLpos : 0 < L := Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hθ0, hθ1⟩)
  set A := Real.log (6 * ρ ^ 4 * μ ^ 4) with hA
  set E := (1 + |A|) / L with hE
  have hEpos : 0 < E := by positivity
  refine ⟨1 + |Real.logb 2 E|, ?_⟩
  intro T hT
  have hT3 : (3 : ℝ) ≤ T := by exact_mod_cast hT
  have hlogT1 : 1 < Real.log (T : ℝ) := by
    have : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; norm_num at this; linarith
    rw [Real.lt_log_iff_exp_lt (by linarith)]; linarith
  have hlogT0 : 0 < Real.log (T : ℝ) := by linarith
  have hloglog : 0 < Real.log (Real.log (T : ℝ)) := Real.log_pos hlogT1
  have hlb : 0 < Real.logb 2 (Real.log (T : ℝ)) :=
    Real.logb_pos (by norm_num) hlogT1
  -- key bound: every round `i ≥ 2` starting before `T` satisfies `2^i < E log T`
  have key : ∀ k : ℕ, roundStart μ ρ T (k + 2) < T →
      ((k + 2 : ℕ) : ℝ) < Real.logb 2 E + Real.logb 2 (Real.log (T : ℝ)) := by
    intro k hk
    have hn : 3 * nRound μ ρ T (k + 1) ≤ roundStart μ ρ T (k + 2) := by
      unfold roundStart
      apply Nat.mul_le_mul_left
      apply Finset.single_le_sum (f := fun j => nRound μ ρ T j) (fun _ _ => Nat.zero_le _)
      simp
    have hnT : (3 * (nRound μ ρ T (k + 1) : ℝ)) < T := by
      have : 3 * nRound μ ρ T (k + 1) < T := lt_of_le_of_lt hn hk
      exact_mod_cast this
    have hD : Delta μ (k + 1) = θ ^ (2 ^ k) / μ := by
      rw [eq_div_iff hμ0.ne', mul_comm]; exact slpe_delta_pow μ k
    have hDpos : 0 < Delta μ (k + 1) := by rw [hD]; positivity
    have hceil : 2 * ρ ^ 4 * Real.log (T : ℝ) / Delta μ (k + 1) ^ 4 ≤ nRound μ ρ T (k + 1) :=
      Nat.le_ceil _
    have hD4 : Delta μ (k + 1) ^ 4 = θ ^ (2 ^ (k + 2)) / μ ^ 4 := by
      rw [hD, div_pow, ← pow_mul]; congr 2; ring
    have h1 : 6 * ρ ^ 4 * μ ^ 4 * Real.log (T : ℝ) < T * θ ^ (2 ^ (k + 2)) := by
      have hq : 0 < θ ^ (2 ^ (k + 2)) := by positivity
      have h0 : 3 * (2 * ρ ^ 4 * Real.log (T : ℝ) / Delta μ (k + 1) ^ 4) < T := by linarith
      have heq : 6 * ρ ^ 4 * μ ^ 4 * Real.log (T : ℝ) =
          3 * (2 * ρ ^ 4 * Real.log (T : ℝ) / Delta μ (k + 1) ^ 4) * θ ^ (2 ^ (k + 2)) := by
        rw [hD4]; field_simp; ring
      rw [heq]; exact mul_lt_mul_of_pos_right h0 hq
    -- take logarithms
    have hpos6 : 0 < 6 * ρ ^ 4 * μ ^ 4 := by positivity
    have hlog := Real.log_lt_log (by positivity) h1
    have e1 : Real.log (6 * ρ ^ 4 * μ ^ 4 * Real.log (T : ℝ)) = A + Real.log (Real.log (T : ℝ)) :=
      Real.log_mul hpos6.ne' hlogT0.ne'
    have e2 : Real.log ((T : ℝ) * θ ^ (2 ^ (k + 2))) =
        Real.log (T : ℝ) + ((2 ^ (k + 2) : ℕ) : ℝ) * Real.log θ := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rw [e1, e2] at hlog
    have hlθ : Real.log θ = -L := by
      rw [hL, one_div, Real.log_inv]; ring
    rw [hlθ] at hlog
    have hA' : -|A| ≤ A := neg_abs_le A
    -- 2^(k+2) * L < log T + |A| ≤ (1 + |A|) log T
    have h3 : ((2 ^ (k + 2) : ℕ) : ℝ) * L < (1 + |A|) * Real.log (T : ℝ) := by
      have : (1 + |A|) * Real.log (T : ℝ) ≥ Real.log (T : ℝ) + |A| := by
        nlinarith [abs_nonneg A]
      nlinarith
    have h4 : ((2 ^ (k + 2) : ℕ) : ℝ) < E * Real.log (T : ℝ) := by
      rw [hE, div_mul_eq_mul_div, lt_div_iff₀ hLpos]; linarith
    have h5 := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) h4
    rw [Real.logb_mul hEpos.ne' hlogT0.ne'] at h5
    have h6 : Real.logb 2 (((2 ^ (k + 2) : ℕ) : ℝ)) = ((k + 2 : ℕ) : ℝ) := by
      push_cast
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; push_cast; ring
    rw [h6] at h5; exact h5
  set X := max 1 (Real.logb 2 E + Real.logb 2 (Real.log (T : ℝ))) with hX
  have hsub : (Finset.Icc 1 T).filter (fun i => roundStart μ ρ T i < T) ⊆
      Finset.Icc 1 ⌊X⌋₊ := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
    refine ⟨hi.1.1, ?_⟩
    apply Nat.le_floor
    rcases Nat.lt_or_ge i 2 with h | h
    · have : i = 1 := by omega
      subst this; simp [hX]
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
      exact le_trans (key k hi.2).le (le_max_right _ _)
  have hcard := Finset.card_le_card hsub
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  unfold iMax
  have hX0 : 0 ≤ X := le_trans zero_le_one (le_max_left _ _)
  calc ((((Finset.Icc 1 T).filter (fun i => roundStart μ ρ T i < T)).card : ℕ) : ℝ)
      ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hcard
    _ ≤ X := Nat.floor_le hX0
    _ ≤ 1 + |Real.logb 2 E| + Real.logb 2 (Real.log (T : ℝ)) := by
        rw [hX]; apply max_le
        · linarith [abs_nonneg (Real.logb 2 E)]
        · linarith [le_abs_self (Real.logb 2 E)]
