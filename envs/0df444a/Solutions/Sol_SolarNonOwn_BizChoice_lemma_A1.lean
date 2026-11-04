-- Prove2me | solution 1 for SolarNonOwn.BizChoice.lemma_A1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T11:13:56.124197+00:00
-- url     : https://prove2.me/submissions/04509c42-8ab6-47be-a335-5e85ec924e68

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_ClosedForms

noncomputable section
open MeasureTheory
open SolarNonOwn.BizChoice

/-- Closed form of the sales-only adoption: the uniform share of `[0,g]` above the
indifference point `(1-α)s/(r+β)`. -/
private lemma adoption0_eq (prm : Params) (h : Measure ℝ) [IsProbabilityMeasure h]
    (hg : 0 < prm.g) (hR : 0 < prm.r + prm.beta) (s : ℝ) :
    adoption0 prm h s =
      (1 / prm.g) * max (prm.g - max ((1 - prm.alpha) * s / (prm.r + prm.beta)) 0) 0 := by
  have hset : {z : ℝ × ℝ | choice0 prm s z.1 z.2 = BizOpt.S} =
      Set.Ici ((1 - prm.alpha) * s / (prm.r + prm.beta)) ×ˢ (Set.univ : Set ℝ) := by
    ext ⟨η, d⟩
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ici, Set.mem_univ, and_true]
    rw [div_le_iff₀ hR]
    unfold choice0
    by_cases hc : cost prm ⟨s, 0, 0⟩ η d .U < cost prm ⟨s, 0, 0⟩ η d .S
    · rw [if_pos hc]
      simp only [cost] at hc
      exact ⟨fun hx => absurd hx (by decide), fun hx => by linarith⟩
    · rw [if_neg hc]
      simp only [cost] at hc
      push Not at hc
      exact ⟨fun _ => by linarith, fun _ => rfl⟩
  have hI : Set.Ici ((1 - prm.alpha) * s / (prm.r + prm.beta)) ∩ Set.Icc 0 prm.g =
      Set.Icc (max ((1 - prm.alpha) * s / (prm.r + prm.beta)) 0) prm.g := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc, max_le_iff]
    tauto
  unfold adoption0 population
  rw [hset, Measure.prod_prod, measure_univ, mul_one, Measure.smul_apply,
    Measure.restrict_apply' measurableSet_Icc, hI, Real.volume_Icc, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal']

theorem solution (prm : Params) (h : Measure ℝ) [IsProbabilityMeasure h]
    (hh : h (Set.Iic 0) = 0) (hs : ModelAssumptions prm) (hα1 : prm.alpha < 1) :
    (∀ c s : ℝ, 0 < profit0 prm h c s → c < C0 prm) ∧
    (∀ c : ℝ, 0 ≤ c → c < C0 prm →
      0 < profit0 prm h c (s0star prm c) ∧
      profit0 prm h c (s0star prm c) = prof0star prm c ∧
      ∀ s : ℝ, profit0 prm h c s ≤ prof0star prm c) ∧
    (∀ a b : ℝ, 0 ≤ a → a < b → b < 1 →
      C0 {prm with alpha := a} < C0 {prm with alpha := b}) ∧
    (∀ a b : ℝ, 0 ≤ a → a < b →
      C0 {prm with beta := a} < C0 {prm with beta := b}) ∧
    (∀ a b : ℝ, 0 ≤ a → a < b →
      C0 {prm with r := a} < C0 {prm with r := b}) := by
  obtain ⟨hα, hβ, ht, htr, hg⟩ := hs
  have hr : 0 < prm.r := lt_trans ht htr
  have hR : 0 < prm.r + prm.beta := by linarith
  have hA : 0 < 1 - prm.alpha := by linarith
  have hadopt := adoption0_eq prm h hg hR
  -- profit in closed form
  have hprof : ∀ c s, profit0 prm h c s =
      (s - c) * ((1 / prm.g) * max (prm.g - max ((1 - prm.alpha) * s / (prm.r + prm.beta)) 0) 0) := by
    intro c s; unfold profit0; rw [hadopt]
  set A := 1 - prm.alpha with hAdef
  set R := prm.r + prm.beta with hRdef
  set g := prm.g with hgdef
  have hC0 : C0 prm = g * R / A := by simp only [C0, hRdef, hAdef, hgdef]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- positive profit forces c < C0
    intro c s hpos
    rw [hprof] at hpos
    have hm : 0 ≤ (1 / g) * max (g - max (A * s / R) 0) 0 := by positivity
    have hm' : 0 < (1 / g) * max (g - max (A * s / R) 0) 0 := by
      rcases eq_or_lt_of_le hm with h0 | h0
      · rw [← h0, mul_zero] at hpos; exact absurd hpos (lt_irrefl _)
      · exact h0
    have hsc : 0 < s - c := pos_of_mul_pos_left hpos hm'.le
    have hmax : 0 < max (g - max (A * s / R) 0) 0 := by
      by_contra hc; push Not at hc
      have : (1 / g) * max (g - max (A * s / R) 0) 0 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
      linarith
    have h1 : A * s / R < g := by
      rcases le_or_gt (g - max (A * s / R) 0) 0 with h2 | h2
      · rw [max_eq_right h2] at hmax; exact absurd hmax (lt_irrefl _)
      · have := le_max_left (A * s / R) 0; linarith
    rw [div_lt_iff₀ hR] at h1
    rw [hC0, lt_div_iff₀ hA]
    nlinarith
  · intro c hc0 hcC
    rw [hC0, lt_div_iff₀ hA] at hcC
    have hY : 0 < g * R - c * A := by linarith
    have hs0 : s0star prm c = (g * R + c * A) / (2 * A) := by
      simp only [s0star, hRdef, hAdef, hgdef]
    have hp0 : prof0star prm c = (g * R - c * A) ^ 2 / (4 * g * A * R) := by
      simp only [prof0star, hRdef, hAdef, hgdef]
    -- value at s0star
    have he : A * s0star prm c / R = (g * R + c * A) / (2 * R) := by
      rw [hs0]; field_simp
    have he0 : 0 ≤ (g * R + c * A) / (2 * R) := by positivity
    have heg : (g * R + c * A) / (2 * R) ≤ g := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hval : profit0 prm h c (s0star prm c) = prof0star prm c := by
      rw [hprof, he, max_eq_left he0, max_eq_left (by linarith), hs0, hp0]
      field_simp
      ring
    refine ⟨?_, hval, ?_⟩
    · rw [hval, hp0]; positivity
    · intro s
      rw [hprof, hp0]
      set e := A * s / R with he_def
      have hse : A * s = e * R := by rw [he_def]; field_simp
      by_cases hneg : e ≤ 0
      · -- full adoption, nonpositive price
        rw [max_eq_right hneg, sub_zero, max_eq_left hg.le]
        have hsnp : s ≤ 0 := by
          by_contra hc; push Not at hc
          have : 0 < A * s := mul_pos hA hc
          nlinarith
        have : (s - c) * (1 / g * g) ≤ 0 := by
          rw [one_div, inv_mul_cancel₀ hg.ne', mul_one]; linarith
        have : 0 ≤ (g * R - c * A) ^ 2 / (4 * g * A * R) := by positivity
        linarith
      · push Not at hneg
        rw [max_eq_left hneg.le]
        by_cases hge : g ≤ e
        · rw [max_eq_right (by linarith), mul_zero, mul_zero]; positivity
        · push Not at hge
          rw [max_eq_left (by linarith)]
          -- AM-GM: (Y - 2X)^2 ≥ 0 with X = A(s-c), Y = gR - Ac
          rw [le_div_iff₀ (by positivity)]
          have key : (s - c) * (1 / g * (g - e)) * (4 * g * A * R) =
              4 * (A * (s - c)) * (g * R - A * s) := by
            rw [hse]; field_simp
          rw [key]
          nlinarith [sq_nonneg (g * R - c * A - 2 * (A * (s - c)))]
  · intro a b ha hab hb1
    simp only [C0]
    have h1 : 0 < 1 - b := by linarith
    have h2 : 0 < prm.g * (prm.r + prm.beta) := by positivity
    exact div_lt_div_of_pos_left h2 h1 (by linarith)
  · intro a b ha hab
    simp only [C0]
    apply div_lt_div_of_pos_right _ hA
    nlinarith
  · intro a b ha hab
    simp only [C0]
    apply div_lt_div_of_pos_right _ hA
    nlinarith
