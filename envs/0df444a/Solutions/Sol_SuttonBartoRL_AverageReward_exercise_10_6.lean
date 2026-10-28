-- Prove2me | solution 1 for SuttonBartoRL.AverageReward.exercise_10_6
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T18:23:37.063209+00:00
-- url     : https://prove2.me/submissions/21967903-dca3-47c5-891e-774a8578116c

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP
import Definitions.Def_SuttonBartoRL_AverageReward_AverageReward

open SuttonBartoRL.AverageReward Filter Topology

theorem ces2 (y : ℕ → ℝ) (hper : ∀ t, y (t + 2) = y t) (hsum : y 0 + y 1 = 1) :
    Tendsto (fun h : ℕ => (1 / (h : ℝ)) * ∑ t ∈ Finset.range h, y t) atTop (𝓝 (1 / 2)) := by
  set c : ℕ → ℝ := fun h => ∑ t ∈ Finset.range h, y t with hc
  have h2 : ∀ h, y h + y (h+1) = 1 := by
    intro h
    induction h with
    | zero => simpa using hsum
    | succ h ih => rw [show h + 1 + 1 = h + 2 by ring, hper]; linarith
  have hc2 : ∀ h, c (h + 2) = c h + 1 := by
    intro h
    simp only [hc, show h + 2 = h + 1 + 1 by ring, Finset.sum_range_succ]
    linarith [h2 h]
  set B := |c 0 - 0| + |c 1 - 1/2|
  have hB : ∀ h, |c h - (h : ℝ) / 2| ≤ B := by
    intro h
    induction h using Nat.strong_induction_on with
    | _ h ih =>
      by_cases hh : h < 2
      · interval_cases h <;> simp only [B] <;> norm_num <;>
          linarith [abs_nonneg (c 0), abs_nonneg (c 1 - 1/2)]
      · obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩
        rw [hc2]
        have := ih k (by omega)
        push_cast
        calc |c k + 1 - ((k : ℝ) + 2) / 2| = |c k - (k : ℝ) / 2| := by ring_nf
          _ ≤ B := this
  have h0 : Tendsto (fun h : ℕ => (1 / (h : ℝ)) * c h - 1 / 2) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun h : ℕ => B / (h : ℝ))
    · filter_upwards [eventually_ge_atTop 1] with h hh
      have hpos : (0 : ℝ) < h := by exact_mod_cast hh
      rw [Real.norm_eq_abs]
      have : (1 / (h : ℝ)) * c h - 1 / 2 = (c h - (h : ℝ) / 2) / h := by field_simp
      rw [this, abs_div, abs_of_pos hpos]
      exact div_le_div_of_nonneg_right (hB h) hpos.le
    · exact tendsto_const_div_atTop_nhds_zero_nat B
  have := h0.add_const (1 / 2)
  simpa using this

theorem diffv2 (y : ℕ → ℝ) (hper : ∀ t, y (t + 2) = y t) (hsum : y 0 + y 1 = 1) :
    ∃ f : ℝ → ℝ, (∀ γ : ℝ, 0 ≤ γ → γ < 1 →
      Tendsto (fun h : ℕ => ∑ t ∈ Finset.range (h + 1), γ ^ t * (y t - 1 / 2)) atTop (𝓝 (f γ))) ∧
      Tendsto f (𝓝[<] 1) (𝓝 ((y 0 - 1 / 2) / 2)) := by
  set a : ℕ → ℝ := fun t => y t - 1 / 2 with ha
  have haper : ∀ t, a (t + 2) = a t := fun t => by simp only [ha, hper]
  set C := |a 0| + |a 1|
  have hC : ∀ t, |a t| ≤ C := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      by_cases ht : t < 2
      · interval_cases t <;> simp only [C] <;> linarith [abs_nonneg (a 0), abs_nonneg (a 1)]
      · obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
        rw [haper]; exact ih k (by omega)
  have hs : ∀ γ : ℝ, 0 ≤ γ → γ < 1 → Summable (fun t => γ ^ t * a t) := by
    intro γ h0 h1
    apply Summable.of_norm_bounded ((summable_geometric_of_lt_one h0 h1).mul_right C)
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 t)]
    exact mul_le_mul_of_nonneg_left (hC t) (pow_nonneg h0 t)
  refine ⟨fun γ => ∑' t, γ ^ t * a t, fun γ h0 h1 => ?_, ?_⟩
  · exact (tendsto_add_atTop_iff_nat 1).2 (hs γ h0 h1).hasSum.tendsto_sum_nat
  · have hform : ∀ γ : ℝ, 0 ≤ γ → γ < 1 → ∑' t, γ ^ t * a t = a 0 / (1 + γ) := by
      intro γ h0 h1
      have hsum2 := ((hs γ h0 h1).sum_add_tsum_nat_add 2).symm
      have e : ∑' t, γ ^ (t + 2) * a (t + 2) = γ ^ 2 * ∑' t, γ ^ t * a t := by
        rw [← tsum_mul_left]; congr 1; funext t; rw [haper, pow_add]; ring
      rw [e] at hsum2
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum2
      have hsa : a 1 = - a 0 := by simp only [ha]; linarith
      rw [hsa] at hsum2
      have hden : 0 < 1 + γ := by linarith
      have h1' : 0 < 1 - γ := by linarith
      rw [eq_div_iff hden.ne']
      have key : (1 - γ) * ((∑' t, γ ^ t * a t) * (1 + γ)) = (1 - γ) * a 0 := by
        nlinarith [hsum2]
      exact mul_left_cancel₀ h1'.ne' key
    have hlim : Tendsto (fun γ : ℝ => a 0 / (1 + γ)) (𝓝[<] 1) (𝓝 ((y 0 - 1 / 2) / 2)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      have hc : ContinuousAt (fun γ : ℝ => a 0 / (1 + γ)) 1 := by
        apply ContinuousAt.div (by fun_prop) (by fun_prop); norm_num
      have := hc.tendsto
      convert this using 2
      simp only [ha]; ring
    apply hlim.congr'
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
    filter_upwards [hmem] with γ hγ
    exact (hform γ hγ.1.le hγ.2).symm

theorem nolim (y : ℕ → ℝ) (h0 : ∀ t, y (2 * t) = y 0) (h1 : ∀ t, y (2 * t + 1) = y 1)
    (hne : y 0 ≠ y 1) : ¬ ∃ L : ℝ, Tendsto y atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hm0 : StrictMono (fun t : ℕ => 2 * t) := fun a b h => by simp only; omega
  have hm1 : StrictMono (fun t : ℕ => 2 * t + 1) := fun a b h => by simp only; omega
  have t0 := hL.comp hm0.tendsto_atTop
  have t1 := hL.comp hm1.tendsto_atTop
  have e0 : (y ∘ fun t : ℕ => 2 * t) = fun _ => y 0 := funext h0
  have e1 : (y ∘ fun t : ℕ => 2 * t + 1) = fun _ => y 1 := funext h1
  rw [e0] at t0; rw [e1] at t1
  have := tendsto_nhds_unique tendsto_const_nhds t0
  have := tendsto_nhds_unique tendsto_const_nhds t1
  exact hne (by linarith)

theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (sA sB : S)
    (hA : ∀ t : ℕ, M.expectedRewardAt π t sA = if Even t then 1 else 0)
    (hB : ∀ t : ℕ, M.expectedRewardAt π t sB = if Even t then 0 else 1) :
    Tendsto (fun h : ℕ => (1 / (h : ℝ)) * ∑ t ∈ Finset.range h, M.expectedRewardAt π t sA)
      atTop (𝓝 (1 / 2)) ∧
    Tendsto (fun h : ℕ => (1 / (h : ℝ)) * ∑ t ∈ Finset.range h, M.expectedRewardAt π t sB)
      atTop (𝓝 (1 / 2)) ∧
    (¬ ∃ L : ℝ, Tendsto (fun t : ℕ => M.expectedRewardAt π t sA) atTop (𝓝 L)) ∧
    (¬ ∃ L : ℝ, Tendsto (fun t : ℕ => M.expectedRewardAt π t sB) atTop (𝓝 L)) ∧
    (¬ ∃ μ : S → ℝ, ∀ s₀ s, Tendsto (fun t : ℕ => M.stateDist π s₀ t s) atTop (𝓝 (μ s))) ∧
    HasDifferentialValue M π (1 / 2) sA (1 / 4) ∧
    HasDifferentialValue M π (1 / 2) sB (-1 / 4) := by
  have ev2 : ∀ t : ℕ, Even (t + 2) ↔ Even t := fun t => by
    rw [Nat.even_add]; simp
  have hpA : ∀ t, M.expectedRewardAt π (t + 2) sA = M.expectedRewardAt π t sA := by
    intro t; rw [hA, hA, if_congr (ev2 t) rfl rfl]
  have hpB : ∀ t, M.expectedRewardAt π (t + 2) sB = M.expectedRewardAt π t sB := by
    intro t; rw [hB, hB, if_congr (ev2 t) rfl rfl]
  have hsA : M.expectedRewardAt π 0 sA + M.expectedRewardAt π 1 sA = 1 := by
    rw [hA, hA]; simp
  have hsB : M.expectedRewardAt π 0 sB + M.expectedRewardAt π 1 sB = 1 := by
    rw [hB, hB]; simp
  have nlA : ¬ ∃ L : ℝ, Tendsto (fun t : ℕ => M.expectedRewardAt π t sA) atTop (𝓝 L) := by
    apply nolim
    · intro t; rw [hA, hA]; simp
    · intro t; rw [hA, hA]; simp
    · rw [hA, hA]; simp
  have nlB : ¬ ∃ L : ℝ, Tendsto (fun t : ℕ => M.expectedRewardAt π t sB) atTop (𝓝 L) := by
    apply nolim
    · intro t; rw [hB, hB]; simp
    · intro t; rw [hB, hB]; simp
    · rw [hB, hB]; simp
  refine ⟨ces2 (fun t => M.expectedRewardAt π t sA) hpA hsA,
    ces2 (fun t => M.expectedRewardAt π t sB) hpB hsB, nlA, nlB, ?_, ?_, ?_⟩
  · rintro ⟨μ, hμ⟩
    apply nlA
    refine ⟨∑ s, μ s * M.policyReward π s, ?_⟩
    have : (fun t : ℕ => M.expectedRewardAt π t sA) =
        fun t => ∑ s, M.stateDist π sA t s * M.policyReward π s := by
      funext t; rfl
    rw [this]
    exact tendsto_finsetSum _ fun s _ => (hμ sA s).mul_const _
  · obtain ⟨f, h1, h2⟩ := diffv2 (fun t => M.expectedRewardAt π t sA) hpA hsA
    refine ⟨f, h1, ?_⟩
    convert h2 using 2
    rw [hA]; norm_num
  · obtain ⟨f, h1, h2⟩ := diffv2 (fun t => M.expectedRewardAt π t sB) hpB hsB
    refine ⟨f, h1, ?_⟩
    convert h2 using 2
    rw [hB]; norm_num
