-- Prove2me | solution 1 for TPG.theorem_1_bias_variance_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:53:42.372985+00:00
-- url     : https://prove2.me/submissions/b056df72-03d4-4ae5-8ee5-110422a9d1eb

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Theorems.Thm_TPG_proposition_5_general_bernoulli_bounds

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

/-- The kernel deviation is nonnegative. -/
private lemma TPG_delta_nonneg {S : Type} [Fintype S] (E : Env S) (T : ℕ) : 0 ≤ E.delta T := by
  unfold Env.delta
  refine Real.iSup_nonneg fun t => Real.iSup_nonneg fun x => ?_
  unfold tvDist
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => abs_nonneg _)

/-- `δ · M ≥ 0`: either the state space is empty and `δ = 0`, or some reward law gives mass
one to `[-M, M]`, which forces `M ≥ 0`. -/
private lemma TPG_delta_mul_bound_nonneg {S : Type} [Fintype S] (E : Env S) (T : ℕ) (M : ℝ)
    (hM : E.RewardBound M) : 0 ≤ E.delta T * M := by
  rcases isEmpty_or_nonempty S with hS | hS
  · have h0 : E.delta T = 0 := by
      unfold Env.delta
      simp [Real.iSup_of_isEmpty]
    rw [h0, zero_mul]
  · obtain ⟨x⟩ := hS
    have hM0 : 0 ≤ M := by
      by_contra h
      have hlt : M < 0 := not_le.1 h
      have h1 := hM x true
      rw [Set.Icc_eq_empty (by linarith), measure_empty] at h1
      exact zero_ne_one h1
    exact mul_nonneg (TPG_delta_nonneg E T) hM0

/-- `Ψ_{n+1}(γ) = ∑_{j<n} (j+1) γ^j`. -/
private lemma TPG_Psi_succ (n : ℕ) (γ : ℝ) :
    Psi (n + 1) γ = ∑ j ∈ Finset.range n, ((j : ℝ) + 1) * γ ^ j := by
  unfold Psi
  rw [Finset.sum_range_succ, if_neg (by omega), add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [if_pos (by have := Finset.mem_range.1 hj; omega)]

/-- Closed form: `(1-γ)² ∑_{j<n} (j+1) γ^j = 1 - (n+1) γ^n + n γ^{n+1}`. -/
private lemma TPG_weighted_geom (n : ℕ) (γ : ℝ) :
    (1 - γ) ^ 2 * ∑ j ∈ Finset.range n, ((j : ℝ) + 1) * γ ^ j
      = 1 - ((n : ℝ) + 1) * γ ^ n + (n : ℝ) * γ ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- `Ψ_k(γ) ≤ (1 - γ^k) / (1 - γ)²` for `0 < γ < 1`. -/
private lemma TPG_Psi_le {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (k : ℕ) :
    Psi k γ ≤ (1 - γ ^ k) / (1 - γ) ^ 2 := by
  have h1 : 0 < 1 - γ := by linarith
  have h2 : 0 < (1 - γ) ^ 2 := by positivity
  rw [le_div_iff₀ h2]
  cases k with
  | zero =>
    have h0 : Psi 0 γ = 0 := by simp [Psi]
    rw [h0, zero_mul, pow_zero, sub_self]
  | succ n =>
    rw [TPG_Psi_succ, mul_comm, TPG_weighted_geom]
    have hn : 0 ≤ γ ^ n := pow_nonneg hγ0.le n
    have hpow : γ ^ (n + 1) = γ ^ n * γ := pow_succ γ n
    have hkey : 0 ≤ ((n : ℝ) + 1) * (γ ^ n * (1 - γ)) :=
      mul_nonneg (by positivity) (mul_nonneg hn h1.le)
    rw [hpow]
    nlinarith [hkey]

theorem solution :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (S : Type) [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
        (E : Env S) (T k : ℕ) (γ M : ℝ),
        0 < T → k ≤ T → 0 < γ → γ < 1 → E.Mixing T γ → E.RewardBound M →
          |(∫ ω, tpgEst (1 / 2) T k ω ∂(E.expLaw T (1 / 2))) - E.gate T|
              ≤ C₁ * ((1 - γ ^ k) / (1 - γ) ^ 2 * (E.delta T) ^ 2 * M
                      + γ ^ k / (1 - γ) * E.delta T * M)
            ∧ variance (tpgEst (1 / 2) T k) (E.expLaw T (1 / 2))
              ≤ C₂ * (((k : ℝ) + 1) ^ 2 * M ^ 2 / (T : ℝ)
                      + γ * ((k : ℝ) + 1) * M ^ 2 / ((T : ℝ) * (1 - γ))) := by
  refine ⟨2, 16, by norm_num, by norm_num, ?_⟩
  intro S _ _ _ E T k γ M hT hk hγ0 hγ1 hmix hM
  have hδ : 0 ≤ E.delta T := TPG_delta_nonneg E T
  have hδM : 0 ≤ E.delta T * M := TPG_delta_mul_bound_nonneg E T M hM
  have h1 : 0 < 1 - γ := by linarith
  have hg : (1 - γ) ≠ 0 := h1.ne'
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hT0 : (T : ℝ) ≠ 0 := hTpos.ne'
  obtain ⟨hbias, hvar, -⟩ := TPG.proposition_5_general_bernoulli_bounds E T k (1 / 2) γ M hT hk
    (by norm_num) (by norm_num) hγ0 hγ1 hmix hM
  constructor
  · refine hbias.trans ?_
    have hzero : |1 - 2 * (1 / 2 : ℝ)| = 0 := by norm_num
    have hcoef : 0 ≤ (E.delta T) ^ 2 * M := by
      have he : (E.delta T) ^ 2 * M = E.delta T * (E.delta T * M) := by ring
      rw [he]
      exact mul_nonneg hδ hδM
    have hmul := mul_le_mul_of_nonneg_left (TPG_Psi_le hγ0 hγ1 k) hcoef
    rw [hzero]
    calc 2 * E.delta T * M * γ ^ k / (1 - γ)
          + 4 * ((1 / 2 : ℝ) ^ 2 + (1 - 1 / 2) ^ 2) * (E.delta T) ^ 2 * M * Psi k γ
          + 2 * 0 * E.delta T * (1 - γ ^ k) / (1 - γ) * E.rDiffNorm
        = 2 * (γ ^ k / (1 - γ) * E.delta T * M)
            + 2 * ((E.delta T) ^ 2 * M * Psi k γ) := by ring
      _ ≤ 2 * (γ ^ k / (1 - γ) * E.delta T * M)
            + 2 * ((E.delta T) ^ 2 * M * ((1 - γ ^ k) / (1 - γ) ^ 2)) := by linarith
      _ = 2 * ((1 - γ ^ k) / (1 - γ) ^ 2 * (E.delta T) ^ 2 * M
            + γ ^ k / (1 - γ) * E.delta T * M) := by ring
  · refine hvar.trans ?_
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have key : M ^ 2 * ((k : ℝ) + 1) / ((T : ℝ) * (1 / 2 * (1 - 1 / 2)))
          * (2 * (k : ℝ) + 3 + 4 * γ / (1 - γ))
        = 16 * (((k : ℝ) + 1) ^ 2 * M ^ 2 / (T : ℝ)
            + γ * ((k : ℝ) + 1) * M ^ 2 / ((T : ℝ) * (1 - γ)))
          - M ^ 2 * ((k : ℝ) + 1) / (T : ℝ) * (8 * (k : ℝ) + 4) := by
      field_simp
      ring
    have hpos : 0 ≤ M ^ 2 * ((k : ℝ) + 1) / (T : ℝ) * (8 * (k : ℝ) + 4) := by positivity
    rw [key]
    linarith
