-- Prove2me | solution 1 for Rudin.ch03_mertens
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-13T15:03:08.348571+00:00
-- url     : https://prove2.me/submissions/aab62c26-4dc9-4fef-a78b-c594d209a3f3

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

open Rudin in
/-- The `N`-th partial sum of the Cauchy product, rewritten as `∑_{k<N} aₖ Bₙ₋ₖ`. -/
private theorem partialSum_cauchy_product (a b : ℕ → ℂ) (N : ℕ) :
    partialSum (fun n => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)) N
      = ∑ k ∈ Finset.range N, a k * partialSum b (N - k) := by
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
      rw [partialSum,
        Finset.sum_range_succ (fun n => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)) N,
        ← partialSum, ih, Finset.sum_range_succ (fun k => a k * b (N - k)) N,
        Finset.sum_range_succ (fun k => a k * partialSum b (N + 1 - k)) N]
      have h1 : ∀ k ∈ Finset.range N,
          a k * partialSum b (N + 1 - k) = a k * partialSum b (N - k) + a k * b (N - k) := by
        intro k hk
        have hk' : k < N := Finset.mem_range.1 hk
        have hsub : N + 1 - k = (N - k) + 1 := by omega
        rw [hsub, partialSum, Finset.sum_range_succ, ← partialSum]
        ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
      have hB1 : partialSum b (N + 1 - N) = b 0 := by
        simp [partialSum]
      rw [hB1, Nat.sub_self]
      ring

/-- If `∑ ‖aₙ‖` has bounded partial sums converging to `α` and `βₘ → 0`, then the twisted sums
`∑_{k<N} aₖ β_{N-k}` tend to `0`. -/
private theorem twisted_sum_tendsto_zero (a β : ℕ → ℂ) (α : ℝ)
    (hS : Tendsto (fun n => ∑ k ∈ Finset.range n, ‖a k‖) atTop (𝓝 α))
    (hβ : Tendsto β atTop (𝓝 0)) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, a k * β (N - k)) atTop (𝓝 0) := by
  set S : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, ‖a k‖ with hSdef
  have hSmono : Monotone S := by
    intro m n hmn
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hmn)) ?_
    intro i _ _
    exact norm_nonneg _
  have hSle : ∀ n, S n ≤ α := fun n => hSmono.ge_of_tendsto hS n
  have hα0 : 0 ≤ α := le_trans (by simp [hSdef]) (hSle 0)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ m, ‖β m‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hβ.norm).bddAbove_range
    exact ⟨M, fun m => hM ⟨m, rfl⟩⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hC0 : 0 < α + M + 1 := by positivity
  set e : ℝ := ε / (2 * (α + M + 1)) with hedef
  have he : 0 < e := by positivity
  obtain ⟨m0, hm0⟩ := Metric.tendsto_atTop.1 hβ e he
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hS e he
  refine ⟨K + m0 + 1, fun N hN => ?_⟩
  set P : ℕ := N - m0 with hPdef
  have hPN : P ≤ N := by omega
  have hKP : K ≤ P := by omega
  have hsplit : ∑ k ∈ Finset.range N, a k * β (N - k)
      = (∑ k ∈ Finset.range P, a k * β (N - k)) + ∑ k ∈ Finset.Ico P N, a k * β (N - k) :=
    (Finset.sum_range_add_sum_Ico _ hPN).symm
  -- first block: the `β` factors are small
  have hb1 : ‖∑ k ∈ Finset.range P, a k * β (N - k)‖ ≤ e * α := by
    have hterm : ∀ k ∈ Finset.range P, ‖a k * β (N - k)‖ ≤ ‖a k‖ * e := by
      intro k hk
      have hk' : k < P := Finset.mem_range.1 hk
      have hge : m0 ≤ N - k := by omega
      have := hm0 (N - k) hge
      rw [dist_eq_norm, sub_zero] at this
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left this.le (norm_nonneg _)
    calc ‖∑ k ∈ Finset.range P, a k * β (N - k)‖
        ≤ ∑ k ∈ Finset.range P, ‖a k * β (N - k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range P, ‖a k‖ * e := Finset.sum_le_sum hterm
      _ = S P * e := by rw [hSdef, ← Finset.sum_mul]
      _ ≤ α * e := by
          exact mul_le_mul_of_nonneg_right (hSle P) he.le
      _ = e * α := mul_comm _ _
  -- second block: the `a` factors have small total mass
  have htail : ∑ k ∈ Finset.Ico P N, ‖a k‖ ≤ e := by
    have hadd : S P + ∑ k ∈ Finset.Ico P N, ‖a k‖ = S N :=
      Finset.sum_range_add_sum_Ico _ hPN
    have h1 : α - S P < e := by
      have := hK P hKP
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.1]
    have h2 : S N ≤ α := hSle N
    linarith
  have hb2 : ‖∑ k ∈ Finset.Ico P N, a k * β (N - k)‖ ≤ M * e := by
    have hterm : ∀ k ∈ Finset.Ico P N, ‖a k * β (N - k)‖ ≤ ‖a k‖ * M := by
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
    calc ‖∑ k ∈ Finset.Ico P N, a k * β (N - k)‖
        ≤ ∑ k ∈ Finset.Ico P N, ‖a k * β (N - k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Ico P N, ‖a k‖ * M := Finset.sum_le_sum hterm
      _ = (∑ k ∈ Finset.Ico P N, ‖a k‖) * M := by rw [Finset.sum_mul]
      _ ≤ e * M := mul_le_mul_of_nonneg_right htail hM0
      _ = M * e := mul_comm _ _
  have hfinal : ‖∑ k ∈ Finset.range N, a k * β (N - k)‖ ≤ e * (α + M) := by
    rw [hsplit]
    calc ‖(∑ k ∈ Finset.range P, a k * β (N - k)) + ∑ k ∈ Finset.Ico P N, a k * β (N - k)‖
        ≤ ‖∑ k ∈ Finset.range P, a k * β (N - k)‖
            + ‖∑ k ∈ Finset.Ico P N, a k * β (N - k)‖ := norm_add_le _ _
      _ ≤ e * α + M * e := add_le_add hb1 hb2
      _ = e * (α + M) := by ring
  have hlt : e * (α + M) < ε := by
    have h1 : e * (α + M) < e * (α + M + 1) := by
      have : (0:ℝ) < e := he
      nlinarith
    have h2 : e * (α + M + 1) = ε / 2 := by
      rw [hedef]
      field_simp
    linarith
  rw [dist_eq_norm, sub_zero]
  exact lt_of_le_of_lt hfinal hlt

/-- Rudin, Theorem 3.50 (Mertens): if `∑ aₙ` converges absolutely to `A`, `∑ bₙ` converges to
`B`, and `cₙ = ∑_{k ≤ n} aₖ bₙ₋ₖ`, then `∑ cₙ` converges to `A B`. -/
theorem solution (a b : ℕ → ℂ) (A B : ℂ)
    (habs : Rudin.SeriesConvergesAbsolutely a) (hA : Rudin.SeriesConvergesTo a A)
    (hB : Rudin.SeriesConvergesTo b B) :
    Rudin.SeriesConvergesTo (fun n => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)) (A * B) := by
  obtain ⟨α, hα⟩ := habs
  have hS : Tendsto (fun n => ∑ k ∈ Finset.range n, ‖a k‖) atTop (𝓝 α) := hα
  set β : ℕ → ℂ := fun m => Rudin.partialSum b m - B with hβdef
  have hβ : Tendsto β atTop (𝓝 0) := by
    have := hB.sub (tendsto_const_nhds (x := B) (f := atTop (α := ℕ)))
    simpa [hβdef] using this
  have hkey : ∀ N, Rudin.partialSum (fun n => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)) N
      = B * Rudin.partialSum a N + ∑ k ∈ Finset.range N, a k * β (N - k) := by
    intro N
    rw [partialSum_cauchy_product a b N]
    have : ∀ k ∈ Finset.range N,
        a k * Rudin.partialSum b (N - k) = B * a k + a k * β (N - k) := by
      intro k _
      simp only [hβdef]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum]
    rfl
  have h1 : Tendsto (fun N => B * Rudin.partialSum a N) atTop (𝓝 (B * A)) :=
    (tendsto_const_nhds (x := B) (f := atTop (α := ℕ))).mul hA
  have h2 : Tendsto (fun N => ∑ k ∈ Finset.range N, a k * β (N - k)) atTop (𝓝 0) :=
    twisted_sum_tendsto_zero a β α hS hβ
  have h3 := h1.add h2
  rw [add_zero] at h3
  have heq : (Rudin.partialSum fun n => ∑ k ∈ Finset.range (n + 1), a k * b (n - k))
      = fun N => B * Rudin.partialSum a N + ∑ k ∈ Finset.range N, a k * β (N - k) := funext hkey
  show Tendsto (Rudin.partialSum fun n => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)) atTop
    (𝓝 (A * B))
  rw [heq, mul_comm A B]
  exact h3
