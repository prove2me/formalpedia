-- Prove2me | solution 1 for ThreeOpSplitting.Accel.stepsize_limit_part1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T16:21:04.157987+00:00
-- url     : https://prove2.me/submissions/eaa5ae1b-c3ce-414a-9b55-590269fa228f

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_Stepsizes

open Filter Topology


namespace ThreeOpSplitting.Accel

noncomputable def nextStep (μB μC η g : ℝ) : ℝ :=
  (-2 * g ^ 2 * μC * η + Real.sqrt ((2 * g ^ 2 * μC * η) ^ 2 + 4 * (1 + 2 * g * μB) * g ^ 2))
    / (2 * (1 + 2 * g * μB))

lemma steps1_succ (μB μC η γ0 : ℝ) (k : ℕ) :
    stepsPart1 μB μC η γ0 (k + 1) = nextStep μB μC η (stepsPart1 μB μC η γ0 k) := rfl

lemma step1_facts (μB μC η g : ℝ) (ha : 0 < μC * η) (hb : 0 ≤ μB) (hg : 0 < g) :
    0 < nextStep μB μC η g ∧
      (1 + 2 * g * μB) * nextStep μB μC η g ^ 2 + 2 * g ^ 2 * (μC * η) * nextStep μB μC η g
        = g ^ 2 := by
  have hc : 0 < 1 + 2 * g * μB := by positivity
  have hΔ0 : 0 ≤ (2 * g ^ 2 * μC * η) ^ 2 + 4 * (1 + 2 * g * μB) * g ^ 2 := by positivity
  have hsq := Real.sq_sqrt hΔ0
  have hdef : 2 * (1 + 2 * g * μB) * nextStep μB μC η g = -2 * g ^ 2 * μC * η +
      Real.sqrt ((2 * g ^ 2 * μC * η) ^ 2 + 4 * (1 + 2 * g * μB) * g ^ 2) := by
    rw [nextStep, mul_div_cancel₀ _ (by positivity)]
  have hgt : 2 * g ^ 2 * μC * η <
      Real.sqrt ((2 * g ^ 2 * μC * η) ^ 2 + 4 * (1 + 2 * g * μB) * g ^ 2) := by
    rw [Real.lt_sqrt (by nlinarith [sq_nonneg g])]
    have : 0 < 4 * (1 + 2 * g * μB) * g ^ 2 := by positivity
    linarith
  set x := nextStep μB μC η g
  set s := Real.sqrt ((2 * g ^ 2 * μC * η) ^ 2 + 4 * (1 + 2 * g * μB) * g ^ 2)
  refine ⟨?_, ?_⟩
  · have : 0 < 2 * (1 + 2 * g * μB) * x := by rw [hdef]; linarith
    have h2 : 0 < 2 * (1 + 2 * g * μB) := by positivity
    exact pos_of_mul_pos_right this h2.le
  · have hs : s = 2 * (1 + 2 * g * μB) * x + 2 * g ^ 2 * μC * η := by linarith
    rw [hs] at hsq
    have h5 : (1 + 2 * g * μB) * ((1 + 2 * g * μB) * x ^ 2 + 2 * g ^ 2 * (μC * η) * x - g ^ 2)
        = 0 := by linear_combination hsq / 4
    rcases mul_eq_zero.1 h5 with h | h
    · linarith
    · linarith

theorem stepsize_limit_part1 (μB μC η γ0 : ℝ)
    (hμB : 0 ≤ μB) (hμC : 0 < μC) (hη0 : 0 < η) (hη1 : η < 1) (hγ0 : 0 < γ0) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) * stepsPart1 μB μC η γ0 k) atTop
      (𝓝 (1 / (μC * η + μB))) := by
  have ha : 0 < μC * η := mul_pos hμC hη0
  set γ := stepsPart1 μB μC η γ0 with hγ
  have hpos : ∀ k, 0 < γ k := by
    intro k
    induction k with
    | zero => exact hγ0
    | succ k ih => rw [hγ, steps1_succ]; exact (step1_facts μB μC η _ ha hμB ih).1
  have hfacts : ∀ k, (1 + 2 * γ k * μB) * γ (k + 1) ^ 2 + 2 * γ k ^ 2 * (μC * η) * γ (k + 1)
      = γ k ^ 2 := by
    intro k
    rw [hγ, steps1_succ]; exact (step1_facts μB μC η _ ha hμB (hpos k)).2
  set a := μC * η with ha_def
  set b := μB with hb_def
  set t : ℕ → ℝ := fun k => 1 / γ k with ht
  have htpos : ∀ k, 0 < t k := fun k => one_div_pos.2 (hpos k)
  -- recursion: t' ^ 2 - t ^ 2 = 2 b t + 2 a t'
  have hrec : ∀ k, t (k + 1) ^ 2 - t k ^ 2 = 2 * b * t k + 2 * a * t (k + 1) := by
    intro k
    have h := hfacts k
    have h1 : γ k ≠ 0 := (hpos k).ne'
    have h2 : γ (k + 1) ≠ 0 := (hpos (k + 1)).ne'
    simp only [ht]
    field_simp
    linear_combination (-1) * h
  have hinc_ge : ∀ k, a ≤ t (k + 1) - t k := by
    intro k
    have h1 := htpos k
    have h2 := htpos (k + 1)
    have hr := hrec k
    have hgt : t k < t (k + 1) := by
      by_contra hle
      push Not at hle
      nlinarith
    nlinarith
  have hinc_le : ∀ k, t (k + 1) - t k ≤ 2 * (a + b) := by
    intro k
    have h1 := htpos k
    have h2 := htpos (k + 1)
    have hr := hrec k
    have hgt : t k ≤ t (k + 1) := by linarith [hinc_ge k]
    nlinarith
  have hlow : ∀ k : ℕ, t 0 + k * a ≤ t k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => push_cast; linarith [hinc_ge k]
  have htinf : Tendsto t atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => t 0 + k * a) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (Tendsto.atTop_mul_const ha tendsto_natCast_atTop_atTop)
    exact tendsto_atTop_mono hlow h1
  have hinv : Tendsto (fun k => (t k)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp htinf
  have hratio : Tendsto (fun k => t (k + 1) / t k) atTop (𝓝 1) := by
    have hup : Tendsto (fun k => 1 + 2 * (a + b) * (t k)⁻¹) atTop (𝓝 (1 + 2 * (a + b) * 0)) :=
      tendsto_const_nhds.add (hinv.const_mul _)
    rw [mul_zero, add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => ?_) (fun k => ?_)
    · have := htpos k
      rw [le_div_iff₀ this]; linarith [hinc_ge k]
    · have := htpos k
      rw [div_le_iff₀ this]
      have := hinc_le k
      field_simp
      nlinarith
  have hinc : Tendsto (fun k => t (k + 1) - t k) atTop (𝓝 (a + b)) := by
    have hform : ∀ k, t (k + 1) - t k = (2 * b + 2 * a * (t (k + 1) / t k)) / (1 + t (k + 1) / t k) := by
      intro k
      have h1 := htpos k
      have h2 := htpos (k + 1)
      rw [eq_div_iff (by positivity)]
      field_simp
      linear_combination hrec k
    have hlim : Tendsto (fun k => (2 * b + 2 * a * (t (k + 1) / t k)) / (1 + t (k + 1) / t k))
        atTop (𝓝 ((2 * b + 2 * a * 1) / (1 + 1))) :=
      (tendsto_const_nhds.add (hratio.const_mul _)).div (tendsto_const_nhds.add hratio)
        (by norm_num)
    rw [show (2 * b + 2 * a * 1) / (1 + 1) = a + b by ring] at hlim
    exact hlim.congr (fun k => (hform k).symm)
  have hab : 0 < a + b := by linarith
  have hces := hinc.cesaro
  have htel : ∀ n : ℕ, ∑ i ∈ Finset.range n, (t (i + 1) - t i) = t n - t 0 :=
    fun n => Finset.sum_range_sub t n
  simp_rw [htel] at hces
  have htn : Tendsto (fun n : ℕ => t n / n) atTop (𝓝 (a + b)) := by
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
  have hfin := hn1.div htn hab.ne'
  rw [one_div] at hfin ⊢
  refine hfin.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnz : (n : ℝ) ≠ 0 := by positivity
  have hg : γ n ≠ 0 := (hpos n).ne'
  simp only [ht, Pi.div_apply]
  field_simp

end ThreeOpSplitting.Accel

open ThreeOpSplitting.Accel

theorem solution (μB μC η γ0 : ℝ)
    (hμB : 0 ≤ μB) (hμC : 0 < μC) (hη0 : 0 < η) (hη1 : η < 1) (hγ0 : 0 < γ0) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) * stepsPart1 μB μC η γ0 k) atTop
      (𝓝 (1 / (μC * η + μB))) := by
  exact stepsize_limit_part1 μB μC η γ0 hμB hμC hη0 hη1 hγ0
