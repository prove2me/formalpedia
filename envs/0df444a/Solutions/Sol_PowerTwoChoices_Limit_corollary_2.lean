-- Prove2me | solution 1 for PowerTwoChoices.Limit.corollary_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:56:46.473212+00:00
-- url     : https://prove2.me/submissions/b3309a5b-8112-4de3-a674-347faf8a5abf

import Mathlib
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem
import Theorems.Thm_PowerTwoChoices_Limit_lemma_2
import Theorems.Thm_PowerTwoChoices_Limit_theorem_2
import Theorems.Thm_PowerTwoChoices_Limit_corollary_1
import Theorems.Thm_PowerTwoChoices_Limit_expected_time_identity

open scoped ENNReal
open Filter Topology
open PowerTwoChoices.Limit

/-- `T_d(λ) = ∑_{i ≥ 0} π_i^d`. -/
private lemma Td_eq_sum_pi_pow (lam : ℝ) (d : ℕ) :
    Td lam d = ∑' i : ℕ, ENNReal.ofReal (fixedPoint lam d i ^ d) := by
  unfold Td
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [show ¬ (1 ≤ 0) from by omega, if_false, zero_add]
  congr 1
  funext i
  simp only [show 1 ≤ i + 1 from by omega, if_true]
  congr 1
  unfold fixedPoint
  rw [← pow_mul, Finset.sum_Ico_eq_sum_range]
  congr 1
  rw [Nat.add_sub_cancel, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← pow_succ, add_comm]

/-- Pointwise: for `a, b ∈ [0,1]`, `|a^d - b^d| ≤ d |a - b|`. -/
private lemma abs_pow_sub_le (d : ℕ) (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : |a ^ d - b ^ d| ≤ d * |a - b| := by
  have h := abs_pow_sub_pow_le a b d
  have hm : max |a| |b| ^ (d - 1) ≤ 1 := by
    apply pow_le_one₀ (le_max_of_le_left (abs_nonneg _))
    rw [abs_of_nonneg ha0, abs_of_nonneg hb0]; exact max_le ha1 hb1
  calc |a ^ d - b ^ d| ≤ |a - b| * d * max |a| |b| ^ (d - 1) := h
    _ ≤ |a - b| * d * 1 := by gcongr
    _ = d * |a - b| := by ring

private lemma ofReal_pow_le (d : ℕ) (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ENNReal.ofReal (a ^ d) ≤ ENNReal.ofReal (b ^ d) + (d : ℝ≥0∞) * ENNReal.ofReal |a - b| := by
  have h := abs_pow_sub_le d a b ha0 ha1 hb0 hb1
  have h2 : a ^ d ≤ b ^ d + d * |a - b| := by
    have := le_abs_self (a ^ d - b ^ d); linarith
  calc ENNReal.ofReal (a ^ d) ≤ ENNReal.ofReal (b ^ d + d * |a - b|) := ENNReal.ofReal_le_ofReal h2
    _ ≤ ENNReal.ofReal (b ^ d) + ENNReal.ofReal (d * |a - b|) := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (b ^ d) + (d : ℝ≥0∞) * ENNReal.ofReal |a - b| := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

private lemma state_le_one {x : ℕ → ℝ} (hx : IsState x) (i : ℕ) : x i ≤ 1 := by
  have := hx.2.2 (Nat.zero_le i); rw [hx.1] at this; exact this

/-- `l1Dist` written as an unconditional sum (the `i = 0` term vanishes for states). -/
private lemma l1Dist_eq (lam : ℝ) (d : ℕ) (x : ℕ → ℝ) (hx : IsState x) :
    l1Dist lam d x = ∑' i : ℕ, ENNReal.ofReal |x i - fixedPoint lam d i| := by
  unfold l1Dist
  congr 1; funext i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [hx.1, fixedPoint]
  · simp [show 1 ≤ i from hi]

private lemma sum_pow_le (d : ℕ) (x y : ℕ → ℝ) (hx : IsState x) (hy : IsState y) :
    ∑' i : ℕ, ENNReal.ofReal (x i ^ d) ≤
      ∑' i : ℕ, ENNReal.ofReal (y i ^ d) +
        (d : ℝ≥0∞) * ∑' i : ℕ, ENNReal.ofReal |x i - y i| := by
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun i =>
    ofReal_pow_le d _ _ (hx.2.1 i) (state_le_one hx i) (hy.2.1 i) (state_le_one hy i)

theorem solution (lam : ℝ) (d : ℕ) (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    Td lam d ≠ ⊤ ∧
    (∀ s : ℝ → ℕ → ℝ, IsTrajectory lam d s → (∃ j : ℕ, s 0 j = 0) →
      Tendsto (fun t => expectedTime d (s t)) atTop (𝓝 (Td lam d))) ∧
    (∀ s : ℝ → ℕ → ℝ, IsTrajectory lam d s → s 0 = emptyState →
      ∀ t : ℝ, 0 ≤ t → expectedTime d (s t) ≤ Td lam d) := by
  obtain ⟨hπ, -, hπsum, -⟩ := lemma_2 lam d hd hlam0 hlam1
  obtain ⟨hT2a, hT2b⟩ := theorem_2 lam d hd hlam0 hlam1
  obtain ⟨w, -, hC1⟩ := corollary_1 lam d hd hlam0 hlam1
  -- π_i → 0
  have hπlim : Tendsto (fixedPoint lam d) atTop (𝓝 0) := hπsum.tendsto_atTop_zero
  -- Finiteness of T_d(λ)
  have hTfin : Td lam d ≠ ⊤ := by
    rw [Td_eq_sum_pi_pow]
    refine ne_top_of_le_ne_top (b := ∑' i : ℕ, ENNReal.ofReal (fixedPoint lam d i)) ?_ ?_
    · rw [← ENNReal.ofReal_tsum_of_nonneg hπ.2.1 hπsum]; exact ENNReal.ofReal_ne_top
    · refine ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal ?_
      exact pow_le_of_le_one (hπ.2.1 i) (state_le_one hπ i) (by omega)
  -- Tails tend to 0 under the doubly exponential bound
  have tails : ∀ s : ℝ → ℕ → ℝ, IsTrajectory lam d s → (∃ j : ℕ, s 0 j = 0) →
      ∀ t : ℝ, 0 ≤ t → Tendsto (s t) atTop (𝓝 0) := by
    intro s hs hj t ht
    obtain ⟨N, α, β, γ, hb⟩ := hT2a s hs hj
    obtain ⟨-, hα0, hα1, hβ, -, hle⟩ := hb t ht
    have h1 : Tendsto (fun i : ℕ => β ^ i) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hβ
    have h2 : Tendsto (fun i : ℕ => α ^ (β ^ i)) atTop (𝓝 0) :=
      (tendsto_rpow_atTop_of_base_lt_one α (by linarith) hα1).comp h1
    have h3 : Tendsto (fun i : ℕ => γ * α ^ (β ^ i)) atTop (𝓝 0) := by
      simpa using h2.const_mul γ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
      (Eventually.of_forall fun i => ((hs.1 t ht).2.1 i)) ?_
    exact eventually_atTop.2 ⟨N, fun i hi => hle i hi⟩
  refine ⟨hTfin, ?_, ?_⟩
  · intro s hs hj
    obtain ⟨δ, hδ, c₀, hc⟩ := (hC1 s hs).2 hj
    -- L(t) → 0
    have hL : Tendsto (fun t => l1Dist lam d (s t)) atTop (𝓝 0) := by
      have hup : Tendsto (fun t : ℝ => ENNReal.ofReal (c₀ * Real.exp (-δ * t))) atTop (𝓝 0) := by
        rw [← ENNReal.ofReal_zero]
        apply ENNReal.tendsto_ofReal
        have : Tendsto (fun t : ℝ => Real.exp (-δ * t)) atTop (𝓝 0) := by
          apply Real.tendsto_exp_atBot.comp
          exact tendsto_id.const_mul_atTop_of_neg (show -δ < 0 by linarith)
        simpa using this.const_mul c₀
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
        (Eventually.of_forall fun _ => zero_le) ?_
      exact eventually_atTop.2 ⟨0, fun t ht => hc t ht⟩
    have hdL : Tendsto (fun t => (d : ℝ≥0∞) * l1Dist lam d (s t)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hL (Or.inr (ENNReal.natCast_ne_top d))
      simpa using this
    rw [ENNReal.tendsto_nhds hTfin]
    intro ε hε
    filter_upwards [(hdL.eventually (gt_mem_nhds (pos_iff_ne_zero.2 (ne_of_gt hε)))),
      eventually_ge_atTop 0] with t hlt ht
    have hst := hs.1 t ht
    rw [expected_time_identity d hd (s t) hst (tails s hs hj t ht), Td_eq_sum_pi_pow]
    rw [Td_eq_sum_pi_pow] at hTfin
    have hL1 := l1Dist_eq lam d (s t) hst
    have hA := sum_pow_le d (s t) (fixedPoint lam d) hst hπ
    have hB := sum_pow_le d (fixedPoint lam d) (s t) hπ hst
    have hsym : ∑' i : ℕ, ENNReal.ofReal |fixedPoint lam d i - s t i| = l1Dist lam d (s t) := by
      rw [hL1]; congr 1; funext i; rw [abs_sub_comm]
    rw [← hL1] at hA
    rw [hsym] at hB
    constructor
    · rw [tsub_le_iff_right]
      exact hB.trans (add_le_add_right hlt.le _)
    · exact hA.trans (add_le_add_right hlt.le _)
  · intro s hs h0 t ht
    have hj : ∃ j : ℕ, s 0 j = 0 := ⟨1, by rw [h0]; simp [emptyState]⟩
    have hst := hs.1 t ht
    rw [expected_time_identity d hd (s t) hst (tails s hs hj t ht), Td_eq_sum_pi_pow]
    refine ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal ?_
    exact pow_le_pow_left₀ (hst.2.1 i) (hT2b s hs h0 t ht i) d
