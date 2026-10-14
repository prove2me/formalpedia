-- Prove2me | solution 1 for TPG.proposition_2_untruncated_pg
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:43:46.164084+00:00
-- url     : https://prove2.me/submissions/c7f12b07-36d4-4d81-b990-bccdaf50e2c9

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Theorems.Thm_TPG_tpg_bias_finite_sum
import Theorems.Thm_TPG_proposition_4_general_bernoulli
import Theorems.Thm_TPG_untruncated_variance_bound

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

/-- Every environment satisfies the mixing condition with contraction constant `1`:
a matrix with nonnegative entries and unit row sums does not increase the `ℓ¹` distance
between two row vectors. -/
private lemma TPG_mixing_one {S : Type} [Fintype S] (E : Env S) (T : ℕ) : E.Mixing T 1 := by
  intro t _ z f f' _ _
  rw [one_mul]
  unfold tvDist
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc ∑ y, |Matrix.vecMul f' (E.P t z) y - Matrix.vecMul f (E.P t z) y|
      = ∑ y, |∑ x, (f' x - f x) * E.P t z x y| := by
        refine Finset.sum_congr rfl fun y _ => ?_
        congr 1
        simp only [Matrix.vecMul, dotProduct]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ ∑ y, ∑ x, |f' x - f x| * E.P t z x y := by
        refine Finset.sum_le_sum fun y _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [abs_mul, abs_of_nonneg (E.P_nonneg t z x y)]
    _ = ∑ x, |f' x - f x| * ∑ y, E.P t z x y := by
        refine Finset.sum_comm.trans ?_
        exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ x, |f' x - f x| :=
        Finset.sum_congr rfl fun x _ => by rw [E.P_row_sum t z x, mul_one]

/-- `Ψ_{n+1}(γ) = ∑_{j<n} (j+1) γ^j`. -/
private lemma TPG_Psi_succ (n : ℕ) (γ : ℝ) :
    Psi (n + 1) γ = ∑ j ∈ Finset.range n, ((j : ℝ) + 1) * γ ^ j := by
  unfold Psi
  rw [Finset.sum_range_succ, if_neg (by omega), add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [if_pos (by have := Finset.mem_range.1 hj; omega)]

/-- `∑_{j<n} (j+1) = n (n+1) / 2`. -/
private lemma TPG_sum_succ (n : ℕ) :
    ∑ j ∈ Finset.range n, ((j : ℝ) + 1) * (1 : ℝ) ^ j = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, one_pow]
    push_cast
    ring

/-- `Ψ_t(1) ≤ T² / 2` for `t ≤ T`. -/
private lemma TPG_Psi_one_le {t T : ℕ} (h : t ≤ T) : Psi t 1 ≤ (T : ℝ) ^ 2 / 2 := by
  cases t with
  | zero =>
    have h0 : Psi 0 1 = 0 := by simp [Psi]
    rw [h0]
    positivity
  | succ n =>
    rw [TPG_Psi_succ, TPG_sum_succ]
    have h1 : (n : ℝ) + 1 ≤ T := by exact_mod_cast h
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) h1]

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

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Type) [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
        (E : Env S) (T : ℕ) (M : ℝ),
        0 < T → E.RewardBound M →
          |(∫ ω, tpgEst (1 / 2) T T ω ∂(E.expLaw T (1 / 2))) - E.gate T|
              ≤ C * ((T : ℝ) ^ 2 * (E.delta T) ^ 2 * M)
            ∧ (∀ g : ℝ, HasDerivAt (fun θ : ℝ => E.J T θ) g (1 / 2) →
                |g - E.gate T| ≤ C * ((T : ℝ) ^ 2 * (E.delta T) ^ 2 * M))
            ∧ variance (tpgEst (1 / 2) T T) (E.expLaw T (1 / 2))
              ≤ 2 * M ^ 2 * ((T : ℝ) + 1) := by
  refine ⟨1, one_pos, ?_⟩
  intro S _ _ _ E T M hT hM
  have hδ : 0 ≤ E.delta T := TPG_delta_nonneg E T
  have hδM : 0 ≤ E.delta T * M := TPG_delta_mul_bound_nonneg E T M hM
  have hcoef : 0 ≤ (E.delta T) ^ 2 * M := by
    have he : (E.delta T) ^ 2 * M = E.delta T * (E.delta T * M) := by ring
    rw [he]
    exact mul_nonneg hδ hδM
  have hbias : |(∫ ω, tpgEst (1 / 2) T T ω ∂(E.expLaw T (1 / 2))) - E.gate T|
      ≤ 1 * ((T : ℝ) ^ 2 * (E.delta T) ^ 2 * M) := by
    have h := TPG.tpg_bias_finite_sum E T T (1 / 2) 1 M hT le_rfl (by norm_num) (by norm_num)
      zero_le_one (TPG_mixing_one E T) hM
    refine h.trans (TPG_avg_le hT _ _ fun t => ?_)
    have ht : (t : ℕ) - T = 0 := Nat.sub_eq_zero_of_le t.isLt.le
    have hmin : min (t : ℕ) T = (t : ℕ) := min_eq_left t.isLt.le
    have hzero : |1 - 2 * (1 / 2 : ℝ)| = 0 := by norm_num
    have hmul := mul_le_mul_of_nonneg_left (TPG_Psi_one_le t.isLt.le) hcoef
    rw [ht, hmin, hzero, Finset.range_zero, Finset.sum_empty]
    calc 2 * E.delta T * M * 1 ^ (t : ℕ) * 0
          + 4 * ((1 / 2 : ℝ) ^ 2 + (1 - 1 / 2) ^ 2) * (E.delta T) ^ 2 * M * Psi (t : ℕ) 1
          + 2 * 0 * E.delta T * (∑ j ∈ Finset.range (t : ℕ), (1 : ℝ) ^ j) * E.rDiffNorm
        = 2 * ((E.delta T) ^ 2 * M * Psi (t : ℕ) 1) := by ring
      _ ≤ 2 * ((E.delta T) ^ 2 * M * ((T : ℝ) ^ 2 / 2)) := by linarith
      _ = 1 * ((T : ℝ) ^ 2 * (E.delta T) ^ 2 * M) := by ring
  refine ⟨hbias, ?_, TPG.untruncated_variance_bound E T M hT hM⟩
  intro g hg
  classical
  have hd := (TPG.proposition_4_general_bernoulli E T T (1 / 2) M hT le_rfl
    (by norm_num) (by norm_num) hM).2.2.2
  rw [hg.unique hd]
  exact hbias
