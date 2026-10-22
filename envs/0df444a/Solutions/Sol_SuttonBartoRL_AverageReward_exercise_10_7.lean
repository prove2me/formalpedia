-- Prove2me | solution 1 for SuttonBartoRL.AverageReward.exercise_10_7
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T18:22:12.995984+00:00
-- url     : https://prove2.me/submissions/15b78673-e3bb-4993-8357-6560ab5bd7dd

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP
import Definitions.Def_SuttonBartoRL_AverageReward_AverageReward
import Definitions.Def_SuttonBartoRL_AverageReward_RingMRP

open SuttonBartoRL.AverageReward Filter Topology

theorem ring_P (s s' : Fin 3) : MDP.policyTrans ringMRP ringPolicy s s' = if s' = s + 1 then 1 else 0 := by
  fin_cases s <;> fin_cases s' <;> simp [MDP.policyTrans, MDP.trans, ringMRP, ringPolicy]

theorem ring_r (s : Fin 3) : MDP.policyReward ringMRP ringPolicy s = if s = 2 then 1 else 0 := by
  fin_cases s <;> simp [MDP.policyReward, MDP.expReward, ringMRP, ringPolicy]

theorem ring_Pv (v : Fin 3 → ℝ) (s : Fin 3) :
    (MDP.policyTrans ringMRP ringPolicy).mulVec v s = v (s + 1) := by
  simp only [Matrix.mulVec, dotProduct, ring_P, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']; simp

def fm (t : ℕ) : Fin 3 := ⟨t % 3, by omega⟩

theorem ring_Ptv (v : Fin 3 → ℝ) : ∀ t : ℕ, ∀ s : Fin 3,
    (MDP.policyTrans ringMRP ringPolicy ^ t).mulVec v s = v (s + fm t) := by
  intro t
  induction t with
  | zero => intro s; simp only [pow_zero, Matrix.one_mulVec]; congr 1; apply Fin.ext; simp [fm]
  | succ t ih =>
    intro s
    rw [pow_succ', ← Matrix.mulVec_mulVec, ring_Pv, ih]
    congr 1
    apply Fin.ext
    simp only [fm, Fin.val_add, Fin.val_one]
    omega

theorem ring_y (t : ℕ) (s : Fin 3) :
    MDP.expectedRewardAt ringMRP ringPolicy t s = if s + fm t = 2 then 1 else 0 := by
  unfold MDP.expectedRewardAt
  rw [ring_Ptv, ring_r]

theorem ces (y : ℕ → ℝ) (hper : ∀ t, y (t + 3) = y t) (hsum : y 0 + y 1 + y 2 = 1) :
    Tendsto (fun h : ℕ => (1 / (h : ℝ)) * ∑ t ∈ Finset.range h, y t) atTop (𝓝 (1 / 3)) := by
  set c : ℕ → ℝ := fun h => ∑ t ∈ Finset.range h, y t with hc
  have h3 : ∀ h, y h + y (h+1) + y (h+2) = 1 := by
    intro h
    induction h with
    | zero => simpa using hsum
    | succ h ih => rw [show h + 1 + 2 = h + 3 by ring, hper]; linarith
  have hc3 : ∀ h, c (h + 3) = c h + 1 := by
    intro h
    simp only [hc, show h + 3 = h + 2 + 1 by ring, Finset.sum_range_succ,
      show h + 2 = h + 1 + 1 by ring]
    linarith [h3 h]
  set B := |c 0 - 0| + |c 1 - 1/3| + |c 2 - 2/3|
  have hB : ∀ h, |c h - (h : ℝ) / 3| ≤ B := by
    intro h
    induction h using Nat.strong_induction_on with
    | _ h ih =>
      by_cases hh : h < 3
      · interval_cases h <;> simp only [B] <;> norm_num <;>
          linarith [abs_nonneg (c 0), abs_nonneg (c 1 - 1/3), abs_nonneg (c 2 - 2/3)]
      · obtain ⟨k, rfl⟩ : ∃ k, h = k + 3 := ⟨h - 3, by omega⟩
        rw [hc3]
        have := ih k (by omega)
        push_cast
        calc |c k + 1 - ((k : ℝ) + 3) / 3| = |c k - (k : ℝ) / 3| := by ring_nf
          _ ≤ B := this
  have h0 : Tendsto (fun h : ℕ => (1 / (h : ℝ)) * c h - 1 / 3) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun h : ℕ => B / (h : ℝ))
    · filter_upwards [eventually_ge_atTop 1] with h hh
      have hpos : (0 : ℝ) < h := by exact_mod_cast hh
      rw [Real.norm_eq_abs]
      have : (1 / (h : ℝ)) * c h - 1 / 3 = (c h - (h : ℝ) / 3) / h := by field_simp
      rw [this, abs_div, abs_of_pos hpos]
      exact div_le_div_of_nonneg_right (hB h) hpos.le
    · exact tendsto_const_div_atTop_nhds_zero_nat B
  have := h0.add_const (1 / 3)
  simpa using this

theorem diffv (y : ℕ → ℝ) (hper : ∀ t, y (t + 3) = y t) (hsum : y 0 + y 1 + y 2 = 1) :
    ∃ f : ℝ → ℝ, (∀ γ : ℝ, 0 ≤ γ → γ < 1 →
      Tendsto (fun h : ℕ => ∑ t ∈ Finset.range (h + 1), γ ^ t * (y t - 1 / 3)) atTop (𝓝 (f γ))) ∧
      Tendsto f (𝓝[<] 1) (𝓝 ((y 0 - y 2) / 3)) := by
  set a : ℕ → ℝ := fun t => y t - 1 / 3 with ha
  have haper : ∀ t, a (t + 3) = a t := fun t => by simp only [ha, hper]
  set C := |a 0| + |a 1| + |a 2|
  have hC : ∀ t, |a t| ≤ C := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      by_cases ht : t < 3
      · interval_cases t <;> simp only [C] <;>
          linarith [abs_nonneg (a 0), abs_nonneg (a 1), abs_nonneg (a 2)]
      · obtain ⟨k, rfl⟩ : ∃ k, t = k + 3 := ⟨t - 3, by omega⟩
        rw [haper]; exact ih k (by omega)
  have hs : ∀ γ : ℝ, 0 ≤ γ → γ < 1 → Summable (fun t => γ ^ t * a t) := by
    intro γ h0 h1
    apply Summable.of_norm_bounded ((summable_geometric_of_lt_one h0 h1).mul_right C)
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 t)]
    exact mul_le_mul_of_nonneg_left (hC t) (pow_nonneg h0 t)
  refine ⟨fun γ => ∑' t, γ ^ t * a t, fun γ h0 h1 => ?_, ?_⟩
  · exact (tendsto_add_atTop_iff_nat 1).2 (hs γ h0 h1).hasSum.tendsto_sum_nat
  · have hform : ∀ γ : ℝ, 0 ≤ γ → γ < 1 →
        ∑' t, γ ^ t * a t = (a 0 - a 2 * γ) / (1 + γ + γ ^ 2) := by
      intro γ h0 h1
      have hsum3 := ((hs γ h0 h1).sum_add_tsum_nat_add 3).symm
      have e : ∑' t, γ ^ (t + 3) * a (t + 3) = γ ^ 3 * ∑' t, γ ^ t * a t := by
        rw [← tsum_mul_left]; congr 1; funext t; rw [haper, pow_add]; ring
      rw [e] at hsum3
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum3
      have hsa : a 0 + a 1 + a 2 = 0 := by simp only [ha]; linarith
      have hden : 0 < 1 + γ + γ ^ 2 := by positivity
      have h1' : 0 < 1 - γ := by linarith
      rw [eq_div_iff hden.ne']
      have key : (1 - γ ^ 3) * ∑' t, γ ^ t * a t = (1 - γ) * (a 0 - a 2 * γ) := by
        have : a 1 = - a 0 - a 2 := by linarith
        rw [this] at hsum3
        nlinarith [hsum3]
      have hfac : 1 - γ ^ 3 = (1 - γ) * (1 + γ + γ ^ 2) := by ring
      rw [hfac, mul_assoc] at key
      have := mul_left_cancel₀ h1'.ne' key
      linarith
    have hlim : Tendsto (fun γ : ℝ => (a 0 - a 2 * γ) / (1 + γ + γ ^ 2)) (𝓝[<] 1)
        (𝓝 ((y 0 - y 2) / 3)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      have hc : ContinuousAt (fun γ : ℝ => (a 0 - a 2 * γ) / (1 + γ + γ ^ 2)) 1 := by
        apply ContinuousAt.div (by fun_prop) (by fun_prop); norm_num
      have := hc.tendsto
      convert this using 2
      simp only [ha]; ring
    apply hlim.congr'
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
    filter_upwards [hmem] with γ hγ
    exact (hform γ hγ.1.le hγ.2).symm

theorem solution :
    (∀ s : Fin 3, Tendsto (fun h : ℕ => (1 / (h : ℝ)) *
        ∑ t ∈ Finset.range h, ringMRP.expectedRewardAt ringPolicy t s) atTop (𝓝 (1 / 3))) ∧
    HasDifferentialValue ringMRP ringPolicy (1 / 3) 0 (-1 / 3) ∧
    HasDifferentialValue ringMRP ringPolicy (1 / 3) 1 0 ∧
    HasDifferentialValue ringMRP ringPolicy (1 / 3) 2 (1 / 3) := by
  have hper : ∀ s : Fin 3, ∀ t, ringMRP.expectedRewardAt ringPolicy (t + 3) s =
      ringMRP.expectedRewardAt ringPolicy t s := by
    intro s t
    rw [ring_y, ring_y]
    have : fm (t + 3) = fm t := by
      apply Fin.ext; simp only [fm]; omega
    rw [this]
  have hsum : ∀ s : Fin 3, ringMRP.expectedRewardAt ringPolicy 0 s +
      ringMRP.expectedRewardAt ringPolicy 1 s + ringMRP.expectedRewardAt ringPolicy 2 s = 1 := by
    intro s; simp only [ring_y]; fin_cases s <;> simp [fm, Fin.ext_iff, Fin.val_add]
  refine ⟨fun s => ces (fun t => ringMRP.expectedRewardAt ringPolicy t s) (hper s) (hsum s), ?_, ?_, ?_⟩
  · obtain ⟨f, h1, h2⟩ := diffv (fun t => ringMRP.expectedRewardAt ringPolicy t 0) (hper 0) (hsum 0)
    refine ⟨f, h1, ?_⟩
    convert h2 using 2
    simp only [ring_y]; simp [fm, Fin.ext_iff]
  · obtain ⟨f, h1, h2⟩ := diffv (fun t => ringMRP.expectedRewardAt ringPolicy t 1) (hper 1) (hsum 1)
    refine ⟨f, h1, ?_⟩
    convert h2 using 2
    simp only [ring_y]; simp [fm, Fin.ext_iff]
  · obtain ⟨f, h1, h2⟩ := diffv (fun t => ringMRP.expectedRewardAt ringPolicy t 2) (hper 2) (hsum 2)
    refine ⟨f, h1, ?_⟩
    convert h2 using 2
    simp only [ring_y]; simp [fm, Fin.ext_iff]
