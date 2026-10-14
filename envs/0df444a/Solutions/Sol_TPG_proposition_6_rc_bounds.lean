-- Prove2me | solution 1 for TPG.proposition_6_rc_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T05:08:52.106055+00:00
-- url     : https://prove2.me/submissions/43e198a3-595e-4f0c-bbe5-8c935c86fa0b

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Theorems.Thm_TPG_rc_bias_finite_sum
import Theorems.Thm_TPG_rc_variance_bound

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

/-- Closed form of the finite geometric sum. -/
private lemma TPG_geom_sum {γ : ℝ} (hγ1 : γ < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, γ ^ j = (1 - γ ^ n) / (1 - γ) := by
  have h : (1 - γ) ≠ 0 := by linarith
  exact eq_div_of_mul_eq h (geom_sum_mul_neg γ n)

/-- The first bias term: `γ^{min t k} G_{t-k}(γ) ≤ γ^k / (1 - γ)`. -/
private lemma TPG_first_term {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (t k : ℕ) :
    γ ^ (min t k) * ∑ j ∈ Finset.range (t - k), γ ^ j ≤ γ ^ k / (1 - γ) := by
  have h1 : 0 < 1 - γ := by linarith
  have hk : 0 ≤ γ ^ k := pow_nonneg hγ0.le k
  rcases le_or_gt t k with h | h
  · rw [Nat.sub_eq_zero_of_le h, Finset.range_zero, Finset.sum_empty, mul_zero]
    exact div_nonneg hk h1.le
  · rw [min_eq_right h.le, TPG_geom_sum hγ1, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ h1.le
    have hn : 0 ≤ γ ^ (t - k) := pow_nonneg hγ0.le _
    nlinarith [mul_nonneg hk hn]

/-- `Ψ_n(γ)` is nondecreasing in `n` for `γ ≥ 0`. -/
private lemma TPG_Psi_mono {γ : ℝ} (hγ0 : 0 ≤ γ) {n m : ℕ} (h : n ≤ m) :
    Psi n γ ≤ Psi m γ := by
  unfold Psi
  have hterm : ∀ j : ℕ, 0 ≤ (if j + 2 ≤ m then ((j : ℝ) + 1) * γ ^ j else 0) := by
    intro j
    split_ifs
    · exact mul_nonneg (by positivity) (pow_nonneg hγ0 j)
    · exact le_rfl
  calc ∑ j ∈ Finset.range n, (if j + 2 ≤ n then ((j : ℝ) + 1) * γ ^ j else 0)
      ≤ ∑ j ∈ Finset.range n, (if j + 2 ≤ m then ((j : ℝ) + 1) * γ ^ j else 0) := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hj : j + 2 ≤ n
        · rw [if_pos hj, if_pos (hj.trans h)]
        · rw [if_neg hj]
          exact hterm j
    _ ≤ ∑ j ∈ Finset.range m, (if j + 2 ≤ m then ((j : ℝ) + 1) * γ ^ j else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun j _ _ => hterm j

/-- An average of numbers each at most `B` is at most `B`. -/
private lemma TPG_avg_le {T : ℕ} (hT : 0 < T) (f : Fin T → ℝ) (B : ℝ) (h : ∀ t, f t ≤ B) :
    (1 / (T : ℝ)) * ∑ t : Fin T, f t ≤ B := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have h1 : ∑ t : Fin T, f t ≤ ∑ _t : Fin T, B := Finset.sum_le_sum fun t _ => h t
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  calc (1 / (T : ℝ)) * ∑ t : Fin T, f t
      ≤ (1 / (T : ℝ)) * ((T : ℝ) * B) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = B := by field_simp

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (θ γ M : ℝ)
    (hT : 0 < T) (hk : k ≤ T) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hmix : E.Mixing T γ) (hM : E.RewardBound M) :
    |(∫ ω, rcEst θ T k ω ∂(E.expLaw T θ)) - E.gate T|
        ≤ 2 * E.delta T * M * γ ^ k / (1 - γ)
          + 4 * (θ ^ 2 + (1 - θ) ^ 2) * (E.delta T) ^ 2 * M * Psi k γ
      ∧ variance (rcEst θ T k) (E.expLaw T θ)
        ≤ M ^ 2 / ((T : ℝ) * (θ * (1 - θ)))
            * (1 + (k : ℝ) * (1 + (1 - 2 * θ) ^ 2 / (θ * (1 - θ))))
            * (2 * (k : ℝ) + 3 + 4 * γ / (1 - γ))
      ∧ (T ≤ k + 1 →
          |(∫ ω, rcEst θ T k ω ∂(E.expLaw T θ)) - E.gate T|
            ≤ 4 * (θ ^ 2 + (1 - θ) ^ 2) * (E.delta T) ^ 2 * M * Psi k γ) := by
  have hδ : 0 ≤ E.delta T := TPG_delta_nonneg E T
  have hδM : 0 ≤ E.delta T * M := TPG_delta_mul_bound_nonneg E T M hM
  have hbias := TPG.rc_bias_finite_sum E T k θ γ M hT hk hθ0 hθ1 hγ0.le hmix hM
  have hvar := TPG.rc_variance_bound E T k θ γ M hT hk hθ0 hθ1 hγ0 hγ1 hmix hM
  -- termwise bounds, uniform in the reward time `t`
  have hA : ∀ t : ℕ,
      2 * E.delta T * M * γ ^ (min t k) * (∑ j ∈ Finset.range (t - k), γ ^ j)
        ≤ 2 * E.delta T * M * γ ^ k / (1 - γ) := by
    intro t
    calc 2 * E.delta T * M * γ ^ (min t k) * (∑ j ∈ Finset.range (t - k), γ ^ j)
        = 2 * (E.delta T * M) * (γ ^ (min t k) * ∑ j ∈ Finset.range (t - k), γ ^ j) := by ring
      _ ≤ 2 * (E.delta T * M) * (γ ^ k / (1 - γ)) :=
          mul_le_mul_of_nonneg_left (TPG_first_term hγ0 hγ1 t k)
            (mul_nonneg (by norm_num) hδM)
      _ = 2 * E.delta T * M * γ ^ k / (1 - γ) := by ring
  have hB : ∀ t : ℕ,
      4 * (θ ^ 2 + (1 - θ) ^ 2) * (E.delta T) ^ 2 * M * Psi (min t k) γ
        ≤ 4 * (θ ^ 2 + (1 - θ) ^ 2) * (E.delta T) ^ 2 * M * Psi k γ := by
    intro t
    have hcoef : 0 ≤ 4 * (θ ^ 2 + (1 - θ) ^ 2) * (E.delta T) ^ 2 * M := by
      have he : 4 * (θ ^ 2 + (1 - θ) ^ 2) * (E.delta T) ^ 2 * M
          = 4 * (θ ^ 2 + (1 - θ) ^ 2) * (E.delta T * (E.delta T * M)) := by ring
      rw [he]
      exact mul_nonneg (by positivity) (mul_nonneg hδ hδM)
    exact mul_le_mul_of_nonneg_left (TPG_Psi_mono hγ0.le (min_le_right t k)) hcoef
  refine ⟨?_, hvar, ?_⟩
  · refine hbias.trans (TPG_avg_le hT _ _ fun t => ?_)
    exact add_le_add (hA t) (hB t)
  · intro hTk
    refine hbias.trans (TPG_avg_le hT _ _ fun t => ?_)
    have ht : (t : ℕ) - k = 0 := by
      have := t.isLt
      omega
    rw [ht, Finset.range_zero, Finset.sum_empty, mul_zero, zero_add]
    exact hB t
