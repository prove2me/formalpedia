-- Prove2me | solution 1 for ThreeOpSplitting.Accel.stepsize_limit_part2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T16:18:33.34821+00:00
-- url     : https://prove2.me/submissions/7b12cd46-0851-495c-902f-620b2d076993

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_Stepsizes

open Filter Topology


namespace ThreeOpSplitting.Accel

lemma steps2_succ (μB LC γ0 : ℝ) (k : ℕ) :
    stepsPart2 μB LC γ0 (k + 1) = stepsPart2 μB LC γ0 k /
      Real.sqrt (1 + 2 * stepsPart2 μB LC γ0 k * (μB - stepsPart2 μB LC γ0 k * LC ^ 2 / 2)) := rfl

lemma steps2_bounds (μB LC γ0 : ℝ) (hμB : 0 < μB) (hLC : 0 < LC) (hγ0 : 0 < γ0)
    (hγ0' : γ0 < 2 * μB / LC ^ 2) (k : ℕ) :
    0 < stepsPart2 μB LC γ0 k ∧ stepsPart2 μB LC γ0 k ≤ γ0 := by
  induction k with
  | zero => exact ⟨hγ0, le_rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    set g := stepsPart2 μB LC γ0 k
    have hgL : g * LC ^ 2 < 2 * μB := by
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < LC ^ 2)).1 (lt_of_le_of_lt h2 hγ0')
      linarith
    have hD : 1 < 1 + 2 * g * (μB - g * LC ^ 2 / 2) := by nlinarith
    have hs : 1 < Real.sqrt (1 + 2 * g * (μB - g * LC ^ 2 / 2)) := by
      rw [Real.lt_sqrt zero_le_one, one_pow]; exact hD
    rw [steps2_succ]
    refine ⟨div_pos h1 (by linarith), ?_⟩
    rw [div_le_iff₀ (by linarith)]
    nlinarith

theorem stepsize_limit_part2 (μB LC γ0 : ℝ)
    (hμB : 0 < μB) (hLC : 0 < LC) (hγ0 : 0 < γ0) (hγ0' : γ0 < 2 * μB / LC ^ 2) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) * stepsPart2 μB LC γ0 k) atTop (𝓝 (1 / μB)) := by
  set γ := stepsPart2 μB LC γ0 with hγ
  have hb := steps2_bounds μB LC γ0 hμB hLC hγ0 hγ0'
  set t : ℕ → ℝ := fun k => 1 / γ k with ht
  have htpos : ∀ k, 0 < t k := fun k => by simp only [ht]; exact one_div_pos.2 (hb k).1
  have ht0 : LC ^ 2 < 2 * μB * t 0 := by
    have : t 0 = 1 / γ0 := rfl
    rw [this, mul_one_div, lt_div_iff₀ hγ0]
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < LC ^ 2)).1 hγ0'
    linarith
  -- the recursion for t
  have hrec : ∀ k, t (k + 1) ^ 2 = t k ^ 2 + 2 * μB * t k - LC ^ 2 := by
    intro k
    have hg := (hb k).1
    have hD : 0 < 1 + 2 * γ k * (μB - γ k * LC ^ 2 / 2) := by
      have hgL : γ k * LC ^ 2 < 2 * μB := by
        have := (lt_div_iff₀ (by positivity : (0:ℝ) < LC ^ 2)).1
          (lt_of_le_of_lt (hb k).2 hγ0')
        linarith
      nlinarith
    have hg' : γ k ≠ 0 := hg.ne'
    simp only [ht]
    rw [hγ, steps2_succ, ← hγ, one_div_div, div_pow, Real.sq_sqrt hD.le]
    field_simp
    ring
  have hmono : ∀ k, t k ≤ t (k + 1) := by
    intro k
    have h1 := (hb (k + 1)).1
    have h2 := (hb k).1
    have hle : γ (k + 1) ≤ γ k := by
      have := steps2_bounds μB LC (γ k) hμB hLC h2 (lt_of_le_of_lt (hb k).2 hγ0') 1
      exact this.2
    simp only [ht]
    exact one_div_le_one_div_of_le h1 hle
  have htmono : Monotone t := monotone_nat_of_le_succ hmono
  set d := 2 * μB * t 0 - LC ^ 2 with hd
  have hdpos : 0 < d := by linarith
  have hsq : ∀ k : ℕ, t 0 ^ 2 + k * d ≤ t k ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hrec k]
      have : t 0 ≤ t k := htmono (Nat.zero_le k)
      push_cast
      nlinarith
  have htinf : Tendsto t atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => Real.sqrt (t 0 ^ 2 + k * d)) atTop atTop := by
      apply Real.tendsto_sqrt_atTop.comp
      apply tendsto_atTop_add_const_left
      exact Tendsto.atTop_mul_const hdpos tendsto_natCast_atTop_atTop
    refine tendsto_atTop_mono (fun k => ?_) h1
    rw [← Real.sqrt_sq (htpos k).le]
    exact Real.sqrt_le_sqrt (hsq k)
  -- increments tend to μB
  have hinc : Tendsto (fun k => t (k + 1) - t k) atTop (𝓝 μB) := by
    have hratio_sq : ∀ k, (t (k + 1) / t k) ^ 2 = 1 + 2 * μB * (t k)⁻¹ - LC ^ 2 * ((t k)⁻¹) ^ 2 := by
      intro k
      have := htpos k
      rw [div_pow, hrec k]
      field_simp
    have hinv : Tendsto (fun k => (t k)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp htinf
    have hratio : Tendsto (fun k => t (k + 1) / t k) atTop (𝓝 1) := by
      have h1 : Tendsto (fun k => 1 + 2 * μB * (t k)⁻¹ - LC ^ 2 * ((t k)⁻¹) ^ 2) atTop
          (𝓝 (1 + 2 * μB * 0 - LC ^ 2 * 0 ^ 2)) := by
        exact ((tendsto_const_nhds.add (hinv.const_mul _)).sub ((hinv.pow 2).const_mul _))
      simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, sub_zero] at h1
      have h2 := h1.sqrt
      rw [Real.sqrt_one] at h2
      refine h2.congr (fun k => ?_)
      rw [← hratio_sq k, Real.sqrt_sq (div_pos (htpos (k + 1)) (htpos k)).le]
    have hform : ∀ k, t (k + 1) - t k =
        (2 * μB - LC ^ 2 * (t k)⁻¹) / (t (k + 1) / t k + 1) := by
      intro k
      have h1 := htpos k
      have h2 := htpos (k + 1)
      have hne : t (k + 1) + t k ≠ 0 := by linarith
      rw [eq_div_iff (by positivity)]
      field_simp
      nlinarith [hrec k]
    have hlim : Tendsto (fun k => (2 * μB - LC ^ 2 * (t k)⁻¹) / (t (k + 1) / t k + 1)) atTop
        (𝓝 ((2 * μB - LC ^ 2 * 0) / (1 + 1))) :=
      (tendsto_const_nhds.sub (hinv.const_mul _)).div (hratio.add tendsto_const_nhds)
        (by norm_num)
    rw [show (2 * μB - LC ^ 2 * 0) / (1 + 1) = μB by ring] at hlim
    exact hlim.congr (fun k => (hform k).symm)
  -- Cesaro
  have hces := hinc.cesaro
  have htel : ∀ n : ℕ, ∑ i ∈ Finset.range n, (t (i + 1) - t i) = t n - t 0 :=
    fun n => Finset.sum_range_sub t n
  simp_rw [htel] at hces
  have htn : Tendsto (fun n : ℕ => t n / n) atTop (𝓝 μB) := by
    have h0 : Tendsto (fun n : ℕ => t 0 * (n : ℝ)⁻¹) atTop (𝓝 (t 0 * 0)) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop |>.const_mul _
    rw [mul_zero] at h0
    have := hces.add h0
    rw [add_zero] at this
    refine this.congr (fun n => ?_)
    ring
  have hn1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 + (n : ℝ)⁻¹) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hfin := hn1.div htn hμB.ne'
  rw [one_div] at hfin ⊢
  refine hfin.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnz : (n : ℝ) ≠ 0 := by positivity
  have hg : γ n ≠ 0 := (hb n).1.ne'
  simp only [ht, Pi.div_apply]
  field_simp

end ThreeOpSplitting.Accel

open ThreeOpSplitting.Accel

theorem solution (μB LC γ0 : ℝ)
    (hμB : 0 < μB) (hLC : 0 < LC) (hγ0 : 0 < γ0) (hγ0' : γ0 < 2 * μB / LC ^ 2) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) * stepsPart2 μB LC γ0 k) atTop (𝓝 (1 / μB)) := by
  exact stepsize_limit_part2 μB LC γ0 hμB hLC hγ0 hγ0'
