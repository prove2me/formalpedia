-- Prove2me | solution 1 for StableDispatch.Markov.drift_outside_Fn
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T12:16:31.066744+00:00
-- url     : https://prove2.me/submissions/ef379a7a-c135-4390-903e-57ee463344d6

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_StableDispatch_Markov_Setting
import Theorems.Thm_StableDispatch_Markov_eq_A_3
import Theorems.Thm_StableDispatch_Markov_eq_A_4

open StableDispatch.Markov

namespace SDDrift

variable {n : ℕ} [NeZero n]

lemma muMax_ge (μ : Fin n → ℝ) (j : Fin n) : μ j ≤ muMax μ :=
  Finset.le_sup' μ (Finset.mem_univ j)

lemma muMin_le (μ : Fin n → ℝ) (j : Fin n) : muMin μ ≤ μ j :=
  Finset.inf'_le μ (Finset.mem_univ j)

lemma muMin_pos (μ : Fin n → ℝ) (hμ : ∀ j, 0 < μ j) : 0 < muMin μ := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty μ
  unfold muMin; rw [hj]; exact hμ j

lemma Fn_finite (lam α : ℝ) (μ : Fin n → ℝ) : (Fn n lam α μ).Finite := by
  set B := (lam * n * (1 + 2 * muMax μ / α) + n + 1) / (2 * min (1 - lam) (muMin μ))
  set N := ⌈B⌉₊
  have hsub : Fn n lam α μ ⊆ (Set.pi Set.univ (fun _ => Set.Iic N)) ×ˢ Set.univ := by
    intro x hx
    simp only [Fn, Set.mem_setOf_eq] at hx
    refine ⟨fun j _ => ?_, Set.mem_univ _⟩
    simp only [Set.mem_Iic]
    have h1 : ((x.1 j : ℕ) : ℝ) ≤ ∑ k, ((x.1 k : ℕ) : ℝ) :=
      Finset.single_le_sum (f := fun k => ((x.1 k : ℕ) : ℝ)) (fun k _ => by positivity)
        (Finset.mem_univ j)
    have h2 : ((x.1 j : ℕ) : ℝ) ≤ N := by
      have := Nat.le_ceil B
      linarith
    exact_mod_cast h2
  exact Set.Finite.subset ((Set.Finite.pi (fun _ => Set.finite_Iic N)).prod Set.finite_univ) hsub

lemma drift_expr_bound (lam α : ℝ) (μ : Fin n → ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hα : 0 < α) (hμ : μ ∈ Sigma n) (q : Fin n → ℕ) (i : Fin n) (hx : (q, i) ∉ Fn n lam α μ) :
    (lam * n * (2 * muMax μ / α) - 2 * muMax μ / α * μ i * (if 1 ≤ q i then 1 else 0)
          - ∑ j, 2 * muMax μ * max ((q i : ℝ) - (q j : ℝ)) 0)
      + (lam * n * (2 * (q i : ℝ) + 1)
          - ∑ j, μ j * (2 * (q j : ℝ) - 1) * (if 1 ≤ q j then 1 else 0)) ≤ -1 := by
  obtain ⟨hμpos, hμsum⟩ := hμ
  set M := muMax μ
  set m := min (1 - lam) (muMin μ)
  set c := 2 * M / α
  have hmpos : 0 < m := lt_min (by linarith) (muMin_pos μ hμpos)
  have hm1 : m ≤ 1 - lam := min_le_left _ _
  have hmμ : ∀ j, m ≤ μ j := fun j => (min_le_right _ _).trans (muMin_le μ j)
  have hM : ∀ j, μ j ≤ M := fun j => muMax_ge μ j
  have hMpos : 0 < M := lt_of_lt_of_le (hμpos i) (hM i)
  have hc : 0 ≤ c := by positivity
  have hn : (0 : ℝ) ≤ n := by positivity
  have hqi : (0 : ℝ) ≤ q i := by positivity
  -- notation
  set Sq := ∑ j, (q j : ℝ)
  set S1 := ∑ j, μ j * (q j : ℝ)
  set S2 := ∑ j, max ((q i : ℝ) - (q j : ℝ)) 0
  set S3 := ∑ j, μ j * max ((q j : ℝ) - (q i : ℝ)) 0
  set S4 := ∑ j, max ((q j : ℝ) - (q i : ℝ)) 0
  have hF5 : lam * n * (1 + c) + n + 1 ≤ 2 * m * Sq := by
    simp only [Fn, Set.mem_setOf_eq, not_lt] at hx
    rw [div_le_iff₀ (by positivity)] at hx
    linarith
  have hF1 : n * (q i : ℝ) + S3 ≤ S1 + M * S2 := by
    have hn' : (n : ℝ) * q i = ∑ j, μ j * (q i : ℝ) := by rw [← Finset.sum_mul, hμsum]
    rw [hn', Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rcases le_total (q j : ℝ) (q i) with h | h
    · rw [max_eq_right (by linarith : (q j : ℝ) - q i ≤ 0), max_eq_left (by linarith)]
      have := hM j
      nlinarith
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ q j - q i), max_eq_right (by linarith)]
      ring_nf; rfl
  have hF2 : m * S4 ≤ S3 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    exact mul_le_mul_of_nonneg_right (hmμ j) (le_max_right _ _)
  have hF3 : Sq ≤ n * (q i : ℝ) + S4 := by
    have hn' : (n : ℝ) * q i = ∑ _j : Fin n, (q i : ℝ) := by simp
    rw [hn', ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have := le_max_left ((q j : ℝ) - q i) 0
    linarith
  have hF4 : 2 * S1 - n ≤ ∑ j, μ j * (2 * (q j : ℝ) - 1) * (if 1 ≤ q j then 1 else 0) := by
    have : 2 * S1 - n = ∑ j, (2 * (μ j * (q j : ℝ)) - μ j) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hμsum]
    rw [this]
    refine Finset.sum_le_sum (fun j _ => ?_)
    split_ifs with h
    · ring_nf; rfl
    · have : q j = 0 := by omega
      rw [this]; simp; exact (hμpos j).le
  have hA3 : 0 ≤ c * μ i * (if 1 ≤ q i then 1 else 0) := by
    have := (hμpos i).le
    split_ifs <;> positivity
  have hS2 : ∑ j, 2 * M * max ((q i : ℝ) - (q j : ℝ)) 0 = 2 * M * S2 := by
    rw [Finset.mul_sum]
  rw [hS2]
  have hp1 : m * (n * (q i : ℝ)) ≤ (1 - lam) * (n * (q i : ℝ)) :=
    mul_le_mul_of_nonneg_right hm1 (by positivity)
  have hp2 : m * Sq ≤ m * (n * (q i : ℝ) + S4) := mul_le_mul_of_nonneg_left hF3 hmpos.le
  nlinarith


end SDDrift

open StableDispatch.Markov in
theorem solution (n : ℕ) [NeZero n] (lam α : ℝ) (μ : Fin n → ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hα : 0 < α) (hμ : μ ∈ Sigma n) :
    (Fn n lam α μ).Finite ∧
      ∀ x : State n, x ∉ Fn n lam α μ →
        ∃ d : ℝ, HasSum (fun y : State n => (Xi μ α y - Xi μ α x) * gen n lam α μ x y) d ∧
          d ≤ -1 := by
  refine ⟨SDDrift.Fn_finite lam α μ, fun x hx => ?_⟩
  obtain ⟨q, i⟩ := x
  obtain ⟨h3, -⟩ := eq_A_3 n lam α μ hlam0 hlam1 hα hμ q i
  obtain ⟨h4, -, -⟩ := eq_A_4 n lam α μ hlam0 hlam1 hα hμ q i
  refine ⟨_, ?_, SDDrift.drift_expr_bound lam α μ hlam0 hlam1 hα hμ q i hx⟩
  have hfun : (fun y : State n => (Xi μ α y - Xi μ α (q, i)) * gen n lam α μ (q, i) y)
      = fun y => (Xi1 μ α y - Xi1 μ α (q, i)) * gen n lam α μ (q, i) y
        + (Xi2 y - Xi2 (q, i)) * gen n lam α μ (q, i) y := by
    funext y; unfold Xi; ring
  rw [hfun]
  exact h3.add h4
