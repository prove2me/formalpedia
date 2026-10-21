-- Prove2me | solution 1 for SaddleSplit.Async.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T16:14:46.643586+00:00
-- url     : https://prove2.me/submissions/d7b4dd4c-fb12-482a-81ef-c690c87da428

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (In : ℕ → Finset I) (hIn : ∀ n, (In n).Nonempty) (Pw : ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : ℕ → E) (hx : Summable fun n => ‖x (n + 1) - x n‖ ^ 2)
    (h0 : In 0 = Finset.univ)
    (hcov : ∀ n, (Finset.range (Pw + 1)).biUnion (fun j => In (n + j)) = Finset.univ)
    (T : ℕ) (i : I) (π : ℕ → ℕ) (hπ : ∀ n, π n ≤ n ∧ n ≤ π n + T) :
    Tendsto (fun n => x (π (Nat.findGreatest (fun j => i ∈ In j) n)) - x n) atTop
      (𝓝 0) := by
  set m : ℕ → ℕ := fun n => Nat.findGreatest (fun j => i ∈ In j) n with hm
  set N := Pw + T with hN
  -- increments tend to zero
  have hd : Tendsto (fun j => ‖x (j + 1) - x j‖) atTop (𝓝 0) := by
    have h2 := hx.tendsto_atTop_zero
    have h3 := h2.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using h3
  -- telescoping bound
  have tele : ∀ a k, ‖x (a + k) - x a‖ ≤ ∑ j ∈ Finset.range k, ‖x (a + j + 1) - x (a + j)‖ := by
    intro a k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      calc ‖x (a + (k + 1)) - x a‖
          = ‖(x (a + k + 1) - x (a + k)) + (x (a + k) - x a)‖ := by
            rw [← add_assoc]; congr 1; abel
        _ ≤ ‖x (a + k + 1) - x (a + k)‖ + ‖x (a + k) - x a‖ := norm_add_le _ _
        _ ≤ _ := by linarith
  -- index bounds
  have hmle : ∀ n, m n ≤ n := fun n => Nat.findGreatest_le n
  have hmlow : ∀ n, Pw ≤ n → n ≤ m n + Pw := by
    intro n hn
    have hc := hcov (n - Pw)
    have hi : i ∈ (Finset.range (Pw + 1)).biUnion (fun j => In (n - Pw + j)) := by
      rw [hc]; exact Finset.mem_univ _
    rw [Finset.mem_biUnion] at hi
    obtain ⟨j, hj, hij⟩ := hi
    rw [Finset.mem_range] at hj
    have hle : n - Pw + j ≤ m n := Nat.le_findGreatest (by omega) hij
    omega
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (N + 1) := by positivity
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.1 hd) _ hδ
  refine ⟨J + N + Pw, fun n hn => ?_⟩
  rw [dist_zero_right]
  set θ := π (m n)
  have hθn : θ ≤ n := (hπ (m n)).1.trans (hmle n)
  have hθlow : n ≤ θ + N := by
    have := hmlow n (by omega)
    have := (hπ (m n)).2
    omega
  obtain ⟨k, hk⟩ : ∃ k, n = θ + k := ⟨n - θ, by omega⟩
  have hkN : k ≤ N := by omega
  have hθJ : J ≤ θ := by omega
  rw [norm_sub_rev, hk]
  refine lt_of_le_of_lt (tele θ k) ?_
  have hterm : ∀ j ∈ Finset.range k, ‖x (θ + j + 1) - x (θ + j)‖ < ε / (N + 1) := by
    intro j _
    have := hJ (θ + j) (by omega)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
  calc ∑ j ∈ Finset.range k, ‖x (θ + j + 1) - x (θ + j)‖
      ≤ ∑ _j ∈ Finset.range k, ε / (N + 1) := Finset.sum_le_sum (fun j hj => (hterm j hj).le)
    _ = k * (ε / (N + 1)) := by simp
    _ < ε := by
      have hk' : (k : ℝ) ≤ N := by exact_mod_cast hkN
      have : (k : ℝ) * (ε / (N + 1)) ≤ N * (ε / (N + 1)) :=
        mul_le_mul_of_nonneg_right hk' hδ.le
      have h2 : (N : ℝ) * (ε / (N + 1)) < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
