-- Prove2me | solution 1 for SLPricing.PreAnn.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T09:50:20.274751+00:00
-- url     : https://prove2.me/submissions/be88635b-2077-4473-bcb4-99992faf46c5

import Mathlib
import Definitions.Def_SLPricing_PreAnn_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLProp1
open SLPricing.PreAnn

lemma prePost_noSL (P : Params) (m : ℝ) : prePost P.noSL m = Measure.dirac 0 := by
  simp [prePost, preVar, Params.noSL, gaussianReal_zero_var]

lemma profit_noSL (P : Params) (p₁ p₂ : ℝ) (B : Set ℝ) :
    preProfit P.noSL p₁ p₂ B = (p₁ - P.c) * mass B + (p₂ - P.c) * lateMass B p₂ 0 := by
  unfold preProfit
  rw [prePost_noSL, integral_dirac]
  rfl

lemma eq_facts (P : Params) (p₁ p₂ : ℝ) (B : Set ℝ) (hB : IsPreEq P.noSL p₁ p₂ B) :
    B ⊆ Icc 0 1 ∧ (∀ x ∈ B, p₁ ≤ x ∧ P.δc * max (x - p₂) 0 ≤ x - p₁) ∧
      (∀ x ∈ Icc (0 : ℝ) 1 \ B, x - p₁ ≤ P.δc * max (x - p₂) 0) := by
  obtain ⟨_, hBsub, hbuy, hdel⟩ := hB
  refine ⟨hBsub, fun x hx => ?_, fun x hx => ?_⟩
  · have h := hbuy x hx
    unfold BuysEarlyPre at h
    rw [prePost_noSL, integral_dirac] at h
    simp only [add_zero] at h
    exact ⟨by linarith [h.1], h.2⟩
  · have h := hdel x hx
    unfold DelaysPre at h
    rw [prePost_noSL, integral_dirac] at h
    simp only [add_zero] at h
    exact h

/-- Mass and late mass of a set sandwiched between `(τ, 1]` and `[τ, 1]`. -/
lemma sandwich (B : Set ℝ) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (h1 : B ⊆ Icc τ 1)
    (h2 : Ioc τ 1 ⊆ B) (p₂ : ℝ) :
    mass B = 1 - τ ∧ lateMass B p₂ 0 = max (τ - max 0 p₂) 0 := by
  constructor
  · unfold mass
    have : volume B = ENNReal.ofReal (1 - τ) := by
      apply le_antisymm
      · exact (measure_mono h1).trans_eq Real.volume_Icc
      · rw [← Real.volume_Ioc]; exact measure_mono h2
    rw [this, ENNReal.toReal_ofReal (by linarith)]
  · unfold lateMass
    set S := {x ∈ Icc (0 : ℝ) 1 \ B | p₂ ≤ x + 0}
    have hS1 : S ⊆ Icc (max 0 p₂) τ := by
      rintro x ⟨⟨hx01, hxB⟩, hx⟩
      refine ⟨max_le hx01.1 (by linarith), ?_⟩
      by_contra h
      push_neg at h
      exact hxB (h2 ⟨h, hx01.2⟩)
    have hS2 : Ico (max 0 p₂) τ ⊆ S := by
      rintro x ⟨hx1, hx2⟩
      have h0 : 0 ≤ x := le_trans (le_max_left _ _) hx1
      refine ⟨⟨⟨h0, by linarith⟩, fun hxB => ?_⟩, by linarith [le_max_right 0 p₂]⟩
      linarith [(h1 hxB).1]
    have : volume S = ENNReal.ofReal (τ - max 0 p₂) := by
      apply le_antisymm
      · exact (measure_mono hS1).trans_eq Real.volume_Icc
      · rw [← Real.volume_Ico]; exact measure_mono hS2
    rw [this, ENNReal.toReal_ofReal']

lemma lt_of_gt_clamp (p x : ℝ) (hx : max 0 (min p 1) < x) (hx1 : x ≤ 1) : p < x := by
  have h1 : min p 1 < x := lt_of_le_of_lt (le_max_right _ _) hx
  rcases le_total p 1 with h | h
  · rw [min_eq_left h] at h1; exact h1
  · rw [min_eq_right h] at h1; linarith

/-- Outside the tie case `δc = 1, p₁ = p₂`, every no-SL equilibrium is a threshold set. -/
lemma exists_tau (P : Params) (hP : P.Standing) (p₁ p₂ : ℝ) (B : Set ℝ)
    (hB : IsPreEq P.noSL p₁ p₂ B) (htie : ¬ (P.δc = 1 ∧ p₁ = p₂)) :
    ∃ τ, 0 ≤ τ ∧ τ ≤ 1 ∧ B ⊆ Icc τ 1 ∧ Ioc τ 1 ⊆ B ∧
      (τ < 1 → p₁ ≤ τ - P.δc * max (τ - p₂) 0) := by
  obtain ⟨hBsub, hbuy, hdel⟩ := eq_facts P p₁ p₂ B hB
  have hδ0 := hP.δc_nonneg
  have hδ1 := hP.δc_le_one
  set δ := P.δc with hδ
  rcases le_or_gt p₁ p₂ with hp | hp
  · -- Case A: p₁ ≤ p₂, threshold p₁
    refine ⟨max 0 (min p₁ 1), le_max_left _ _, max_le zero_le_one (min_le_right _ _), ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨max_le (hBsub hx).1 (le_trans (min_le_left _ _) (hbuy x hx).1), (hBsub hx).2⟩
    · intro x hx
      by_contra hxB
      have hx0 : 0 ≤ x := le_trans (le_max_left _ _) hx.1.le
      have hd := hdel x ⟨⟨hx0, hx.2⟩, hxB⟩
      have hxp := lt_of_gt_clamp p₁ x hx.1 hx.2
      rcases le_or_gt x p₂ with hx2 | hx2
      · rw [max_eq_right (by linarith), mul_zero] at hd; linarith
      · rw [max_eq_left (by linarith)] at hd
        have : δ * (x - p₂) ≤ x - p₂ := mul_le_of_le_one_left (by linarith) hδ1
        have hpe : p₁ = p₂ := by linarith
        apply htie
        refine ⟨?_, hpe⟩
        by_contra hne
        have hlt : δ < 1 := lt_of_le_of_ne hδ1 hne
        rw [hpe] at hd
        have : 0 < (1 - δ) * (x - p₂) := mul_pos (by linarith) (by linarith)
        nlinarith
    · intro hτ
      have hp1 : p₁ < 1 := by
        by_contra h; push_neg at h
        rw [min_eq_right h, max_eq_right zero_le_one] at hτ; exact lt_irrefl _ hτ
      rw [min_eq_left hp1.le]
      rcases le_total 0 p₁ with h0 | h0
      · rw [max_eq_right h0, max_eq_right (by linarith : p₁ - p₂ ≤ 0), mul_zero]; linarith
      · rw [max_eq_left h0]
        rcases le_total 0 p₂ with h2 | h2
        · rw [max_eq_right (by linarith : (0:ℝ) - p₂ ≤ 0), mul_zero]; linarith
        · rw [max_eq_left (by linarith : (0:ℝ) ≤ 0 - p₂)]; nlinarith
  · rcases lt_or_eq_of_le hδ1 with hlt | heq
    · -- Case B: p₂ < p₁, δ < 1
      set r := (p₁ - δ * p₂) / (1 - δ) with hr
      have hr' : (1 - δ) * r = p₁ - δ * p₂ := by
        rw [hr]; field_simp [show (1 - δ) ≠ 0 by linarith]
      have hrp : p₁ ≤ r := by
        have e : (1 - δ) * (r - p₁) = δ * (p₁ - p₂) := by rw [mul_sub, hr']; ring
        have h0 : 0 ≤ δ * (p₁ - p₂) := mul_nonneg hδ0 (by linarith)
        by_contra h; push_neg at h
        have : (1 - δ) * (r - p₁) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
        linarith
      refine ⟨max 0 (min r 1), le_max_left _ _, max_le zero_le_one (min_le_right _ _), ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨hx1, hx2⟩ := hbuy x hx
        rw [max_eq_left (by linarith)] at hx2
        have : r ≤ x := by
          by_contra h; push_neg at h
          have : (1 - δ) * x < (1 - δ) * r := mul_lt_mul_of_pos_left h (by linarith)
          linarith
        exact ⟨max_le (hBsub hx).1 (le_trans (min_le_left _ _) this), (hBsub hx).2⟩
      · intro x hx
        by_contra hxB
        have hx0 : 0 ≤ x := le_trans (le_max_left _ _) hx.1.le
        have hd := hdel x ⟨⟨hx0, hx.2⟩, hxB⟩
        have hxr := lt_of_gt_clamp r x hx.1 hx.2
        rw [max_eq_left (by linarith)] at hd
        have : (1 - δ) * r < (1 - δ) * x := mul_lt_mul_of_pos_left hxr (by linarith)
        linarith
      · intro hτ
        have hr1 : r < 1 := by
          by_contra h; push_neg at h
          rw [min_eq_right h, max_eq_right zero_le_one] at hτ; exact lt_irrefl _ hτ
        rw [min_eq_left hr1.le]
        rcases le_total 0 r with h0 | h0
        · rw [max_eq_right h0, max_eq_left (by linarith : (0:ℝ) ≤ r - p₂)]; linarith
        · rw [max_eq_left h0, max_eq_left (by linarith : (0:ℝ) ≤ 0 - p₂)]; nlinarith
    · -- Case C: p₂ < p₁, δ = 1 : nobody buys early
      refine ⟨1, zero_le_one, le_refl _, ?_, ?_, fun h => absurd h (lt_irrefl _)⟩
      · intro x hx
        obtain ⟨hx1, hx2⟩ := hbuy x hx
        rw [heq, one_mul, max_eq_left (by linarith)] at hx2
        linarith
      · intro x hx; exact absurd (lt_of_lt_of_le hx.1 hx.2) (lt_irrefl _)

/-- The real optimisation problem. -/
lemma real_F (τ p₁ p₂ δ c : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hu : τ < 1 → p₁ ≤ τ - δ * max (τ - p₂) 0) :
    (p₁ - c) * (1 - τ) + (p₂ - c) * max (τ - max 0 p₂) 0 ≤ (1 - c) ^ 2 / (δ + 3) ∧
      (δ < 1 → (p₁ - c) * (1 - τ) + (p₂ - c) * max (τ - max 0 p₂) 0 = (1 - c) ^ 2 / (δ + 3) →
        p₁ = (c * (1 + δ) + 2) / (δ + 3) ∧ p₂ = (2 * c + δ + 1) / (δ + 3)) := by
  have hD : 0 < δ + 3 := by linarith
  have hw : 0 < 1 - c := by linarith
  have h4 : (1 - c) ^ 2 / 4 ≤ (1 - c) ^ 2 / (δ + 3) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hD (by linarith)
  have h4s : δ < 1 → (1 - c) ^ 2 / 4 < (1 - c) ^ 2 / (δ + 3) := fun h =>
    div_lt_div_of_pos_left (by positivity) hD (by linarith)
  set Pr := (p₁ - c) * (1 - τ) + (p₂ - c) * max (τ - max 0 p₂) 0 with hPr
  -- either the profit is at most (1-c)²/4, or we are in the interior case
  have hcase : Pr ≤ (1 - c) ^ 2 / 4 ∨ (τ < 1 ∧ 0 ≤ p₂ ∧ p₂ ≤ τ) := by
    rcases eq_or_lt_of_le hτ1 with hτ | hτ
    · left
      rw [hPr, hτ, sub_self, mul_zero, zero_add]
      rcases le_total p₂ 0 with h | h
      · rw [max_eq_left h]
        have : (p₂ - c) * max (1 - 0) 0 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_max_right _ _)
        exact le_trans this (by positivity)
      · rw [max_eq_right h]
        rcases le_total (1 - p₂) 0 with h' | h'
        · rw [max_eq_right h', mul_zero]; positivity
        · rw [max_eq_left h']; nlinarith [sq_nonneg (2 * p₂ - 1 - c)]
    · have hq := hu hτ
      have hfirst : (p₁ - c) * (1 - τ) ≤ (τ - δ * max (τ - p₂) 0 - c) * (1 - τ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      rcases lt_or_ge p₂ 0 with h | h
      · left
        have e2 : max (τ - p₂) 0 = τ - p₂ := max_eq_left (by linarith)
        rw [hPr, max_eq_left h.le, sub_zero, max_eq_left hτ0]
        rw [e2] at hfirst
        have : (p₂ - c) * τ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hτ0
        have : (τ - δ * (τ - p₂) - c) * (1 - τ) ≤ (τ - c) * (1 - τ) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
        nlinarith [sq_nonneg (2 * τ - 1 - c)]
      · rcases le_or_gt p₂ τ with h' | h'
        · right; exact ⟨hτ, h, h'⟩
        · left
          rw [hPr, max_eq_right h, max_eq_right (by linarith : τ - p₂ ≤ 0), mul_zero, add_zero]
          rw [max_eq_right (by linarith : τ - p₂ ≤ 0), mul_zero, sub_zero] at hfirst
          nlinarith [sq_nonneg (2 * τ - 1 - c)]
  rcases hcase with hle | ⟨hτ, h0, h'⟩
  · refine ⟨le_trans hle h4, fun hδ hEq => ?_⟩
    have := h4s hδ; linarith
  · have hq := hu hτ
    rw [max_eq_left (by linarith : 0 ≤ τ - p₂)] at hq
    have hfirst : (p₁ - c) * (1 - τ) ≤ (τ - δ * (τ - p₂) - c) * (1 - τ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hPr' : Pr = (p₁ - c) * (1 - τ) + (p₂ - c) * (τ - p₂) := by
      rw [hPr, max_eq_right h0, max_eq_left (by linarith)]
    set a := τ - (c + 2 + δ) / (δ + 3) with ha
    set b := p₂ - (2 * c + δ + 1) / (δ + 3) with hb
    clear_value a b
    have key : (1 - c) ^ 2 / (δ + 3) - ((τ - δ * (τ - p₂) - c) * (1 - τ) + (p₂ - c) * (τ - p₂))
        = (1 - δ) * (a - b / 2) ^ 2 + (3 + δ) * b ^ 2 / 4 := by
      rw [ha, hb]; field_simp; ring
    have hS : 0 ≤ (1 - δ) * (a - b / 2) ^ 2 + (3 + δ) * b ^ 2 / 4 := by
      have := mul_nonneg (by linarith : 0 ≤ 1 - δ) (sq_nonneg (a - b / 2))
      have := sq_nonneg b
      nlinarith
    refine ⟨by rw [hPr']; linarith, fun hδ hEq => ?_⟩
    rw [hPr'] at hEq
    have hS0 : (1 - δ) * (a - b / 2) ^ 2 + (3 + δ) * b ^ 2 / 4 = 0 := by
      apply le_antisymm _ hS; linarith
    have hX := mul_nonneg (by linarith : 0 ≤ 1 - δ) (sq_nonneg (a - b / 2))
    have hY := mul_nonneg (by linarith : (0:ℝ) ≤ 3 + δ) (sq_nonneg b)
    have hb0 : b = 0 := by
      have hY0 : (3 + δ) * b ^ 2 = 0 := by linarith
      rcases mul_eq_zero.1 hY0 with h | h
      · linarith
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    have ha0 : a = 0 := by
      have hX0 : (1 - δ) * (a - b / 2) ^ 2 = 0 := by linarith
      rw [hb0, zero_div, sub_zero] at hX0
      rcases mul_eq_zero.1 hX0 with h | h
      · linarith
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    have hτe : τ = (c + 2 + δ) / (δ + 3) := by
      have := ha0; rw [ha] at this; exact sub_eq_zero.1 this
    have hpe : p₂ = (2 * c + δ + 1) / (δ + 3) := by
      have := hb0; rw [hb] at this; exact sub_eq_zero.1 this
    have hτlt : 0 < 1 - τ := by linarith
    have hp1 : p₁ = τ - δ * (τ - p₂) := by
      have hge : (τ - δ * (τ - p₂) - c) * (1 - τ) ≤ (p₁ - c) * (1 - τ) := by
        have : (1 - c) ^ 2 / (δ + 3) - ((τ - δ * (τ - p₂) - c) * (1 - τ) +
          (p₂ - c) * (τ - p₂)) = 0 := by rw [key, hS0]
        linarith
      have := le_of_mul_le_mul_right hge hτlt
      linarith
    refine ⟨?_, hpe⟩
    rw [hp1, hτe, hpe]; field_simp; ring

/-- The tie case `δc = 1`, `p₁ = p₂`. -/
lemma tie_bound (P : Params) (hP : P.Standing) (p : ℝ) (B : Set ℝ)
    (hB : IsPreEq P.noSL p p B) : preProfit P.noSL p p B ≤ (1 - P.c) ^ 2 / 4 := by
  obtain ⟨hBsub, hbuy, _⟩ := eq_facts P p p B hB
  have hBm : MeasurableSet B := hB.1
  rw [profit_noSL]
  unfold mass lateMass
  set S := {x ∈ Icc (0 : ℝ) 1 \ B | p ≤ x + 0}
  have hdisj : Disjoint B S := by
    rw [Set.disjoint_left]; intro x hx hS; exact hS.1.2 hx
  have hSm : MeasurableSet S := by
    refine (measurableSet_Icc.diff hBm).inter ?_
    exact measurableSet_le measurable_const (measurable_id.add measurable_const)
  have hunion : B ∪ S = Icc (max 0 p) 1 := by
    ext x
    simp only [mem_union, mem_Icc, max_le_iff]
    constructor
    · rintro (hx | hx)
      · exact ⟨⟨(hBsub hx).1, (hbuy x hx).1⟩, (hBsub hx).2⟩
      · obtain ⟨⟨hx1, _⟩, hx2⟩ := hx
        exact ⟨⟨hx1.1, by linarith⟩, hx1.2⟩
    · rintro ⟨⟨h0, hp⟩, h1⟩
      by_cases hx : x ∈ B
      · exact Or.inl hx
      · exact Or.inr ⟨⟨⟨h0, h1⟩, hx⟩, by linarith⟩
  have hBt : volume B ≠ ⊤ := ((measure_mono hBsub).trans_lt measure_Icc_lt_top).ne
  have hSt : volume S ≠ ⊤ :=
    ((measure_mono (fun x hx => hx.1.1 : S ⊆ Icc 0 1)).trans_lt measure_Icc_lt_top).ne
  have hvol : (volume B).toReal + (volume S).toReal = max (1 - max 0 p) 0 := by
    rw [← ENNReal.toReal_add hBt hSt,
      ← measure_union hdisj hSm, hunion, Real.volume_Icc, ENNReal.toReal_ofReal']
  have : (p - P.c) * (volume B).toReal + (p - P.c) * (volume S).toReal =
      (p - P.c) * max (1 - max 0 p) 0 := by rw [← mul_add, hvol]
  rw [this]
  have hc0 := hP.c_nonneg
  rcases le_total p 0 with h | h
  · rw [max_eq_left h, sub_zero, max_eq_left zero_le_one]; nlinarith [sq_nonneg (1 - P.c)]
  · rw [max_eq_right h]
    rcases le_total (1 - p) 0 with h' | h'
    · rw [max_eq_right h', mul_zero]; positivity
    · rw [max_eq_left h']; nlinarith [sq_nonneg (2 * p - 1 - P.c)]

lemma main_bound (P : Params) (hP : P.Standing) (p₁ p₂ : ℝ) (B : Set ℝ)
    (hB : IsPreEq P.noSL p₁ p₂ B) :
    preProfit P.noSL p₁ p₂ B ≤ (1 - P.c) ^ 2 / (P.δc + 3) ∧
      (P.δc < 1 → preProfit P.noSL p₁ p₂ B = (1 - P.c) ^ 2 / (P.δc + 3) →
        p₁ = (P.c * (1 + P.δc) + 2) / (P.δc + 3) ∧ p₂ = (2 * P.c + P.δc + 1) / (P.δc + 3)) := by
  by_cases htie : P.δc = 1 ∧ p₁ = p₂
  · obtain ⟨h1, h2⟩ := htie
    subst h2
    refine ⟨?_, fun h => absurd h (by rw [h1]; exact lt_irrefl _)⟩
    rw [h1]; norm_num
    exact tie_bound P hP p₁ B hB
  · obtain ⟨τ, hτ0, hτ1, h1, h2, hu⟩ := exists_tau P hP p₁ p₂ B hB htie
    obtain ⟨hm, hl⟩ := sandwich B τ hτ0 hτ1 h1 h2 p₂
    rw [profit_noSL, hm, hl]
    exact real_F τ p₁ p₂ P.δc P.c hτ0 hτ1 hP.δc_nonneg hP.δc_le_one hP.c_nonneg hP.c_lt_one hu

/-- The optimal plan and its equilibrium. -/
lemma opt_plan (P : Params) (hP : P.Standing) :
    IsPreEq P.noSL ((P.c * (1 + P.δc) + 2) / (P.δc + 3)) ((2 * P.c + P.δc + 1) / (P.δc + 3))
      (Icc ((P.c + 2 + P.δc) / (P.δc + 3)) 1) ∧
    preProfit P.noSL ((P.c * (1 + P.δc) + 2) / (P.δc + 3)) ((2 * P.c + P.δc + 1) / (P.δc + 3))
      (Icc ((P.c + 2 + P.δc) / (P.δc + 3)) 1) = (1 - P.c) ^ 2 / (P.δc + 3) := by
  have hδ0 := hP.δc_nonneg
  have hδ1 := hP.δc_le_one
  have hc0 := hP.c_nonneg
  have hc1 := hP.c_lt_one
  set δ := P.δc
  set c := P.c
  have hD : 0 < δ + 3 := by linarith
  set τ := (c + 2 + δ) / (δ + 3) with hτ
  set p₁ := (c * (1 + δ) + 2) / (δ + 3) with hp₁
  set p₂ := (2 * c + δ + 1) / (δ + 3) with hp₂
  have e1 : τ - p₁ = δ * (1 - c) / (δ + 3) := by rw [hτ, hp₁]; field_simp; ring
  have e2 : τ - p₂ = (1 - c) / (δ + 3) := by rw [hτ, hp₂]; field_simp; ring
  have e3 : p₁ - δ * p₂ = (1 - δ) * τ := by rw [hτ, hp₁, hp₂]; field_simp; ring
  have e4 : p₁ - p₂ = (1 - c) * (1 - δ) / (δ + 3) := by rw [hp₁, hp₂]; field_simp; ring
  have hτp₁ : p₁ ≤ τ := by
    have : 0 ≤ δ * (1 - c) / (δ + 3) := div_nonneg (mul_nonneg hδ0 (by linarith)) hD.le
    linarith
  have hτp₂ : p₂ < τ := by
    have : 0 < (1 - c) / (δ + 3) := div_pos (by linarith) hD
    linarith
  have hp₁p₂ : p₂ ≤ p₁ := by
    have : 0 ≤ (1 - c) * (1 - δ) / (δ + 3) :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) hD.le
    linarith
  have hτ1 : τ ≤ 1 := by rw [hτ, div_le_one hD]; linarith
  have hτ1' : τ < 1 := by rw [hτ, div_lt_one hD]; linarith
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hp₂0 : 0 ≤ p₂ := by rw [hp₂]; positivity
  have hEq : IsPreEq P.noSL p₁ p₂ (Icc τ 1) := by
    refine ⟨measurableSet_Icc, fun x hx => ⟨le_trans hτ0 hx.1, hx.2⟩, ?_, ?_⟩
    · intro x hx
      unfold BuysEarlyPre
      rw [prePost_noSL, integral_dirac]
      simp only [add_zero]
      refine ⟨by linarith [hx.1], ?_⟩
      show δ * max (x - p₂) 0 ≤ x - p₁
      rw [max_eq_left (by linarith [hx.1])]
      nlinarith [hx.1]
    · intro x hx
      unfold DelaysPre
      rw [prePost_noSL, integral_dirac]
      simp only [add_zero]
      show x - p₁ ≤ δ * max (x - p₂) 0
      have hxτ : x < τ := by
        by_contra h; push_neg at h; exact hx.2 ⟨h, hx.1.2⟩
      rcases le_total x p₂ with h | h
      · rw [max_eq_right (by linarith)]; linarith
      · rw [max_eq_left (by linarith)]; nlinarith
  refine ⟨hEq, ?_⟩
  obtain ⟨hm, hl⟩ := sandwich (Icc τ 1) τ hτ0 hτ1 (le_refl _) Ioc_subset_Icc_self p₂
  rw [profit_noSL, hm, hl, max_eq_right hp₂0, max_eq_left (by linarith)]
  show (p₁ - c) * (1 - τ) + (p₂ - c) * (τ - p₂) = (1 - c) ^ 2 / (δ + 3)
  rw [hτ, hp₁, hp₂]; field_simp; ring

lemma value_eq (P : Params) (hP : P.Standing) :
    preValue P.noSL = (((1 - P.c) ^ 2 / (P.δc + 3) : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨⟨p₁, p₂, B⟩, hB⟩
    exact EReal.coe_le_coe_iff.2 (main_bound P hP p₁ p₂ B hB).1
  · obtain ⟨hEq, hpr⟩ := opt_plan P hP
    rw [← hpr]
    exact le_iSup (fun o : {o : ℝ × ℝ × Set ℝ // IsPreEq P.noSL o.1 o.2.1 o.2.2} =>
      ((preProfit P.noSL o.1.1 o.1.2.1 o.1.2.2 : ℝ) : EReal)) ⟨(_, _, _), hEq⟩

end SLProp1

open SLPricing.PreAnn SLProp1

theorem solution (P : Params) (hP : P.Standing) :
    preValue P.noSL = (((1 - P.c) ^ 2 / (P.δc + 3) : ℝ) : EReal) ∧
      IsOptimalPre P.noSL ((P.c * (1 + P.δc) + 2) / (P.δc + 3))
        ((2 * P.c + P.δc + 1) / (P.δc + 3)) ∧
      (P.δc < 1 → ∀ p₁ p₂ : ℝ, IsOptimalPre P.noSL p₁ p₂ →
        p₁ = (P.c * (1 + P.δc) + 2) / (P.δc + 3) ∧ p₂ = (2 * P.c + P.δc + 1) / (P.δc + 3)) ∧
      StrictAntiOn (fun d : ℝ => (P.c * (1 + d) + 2) / (d + 3)) (Icc 0 1) ∧
      StrictMonoOn (fun d : ℝ => (2 * P.c + d + 1) / (d + 3)) (Icc 0 1) ∧
      StrictAntiOn (fun d : ℝ => preValue (P.withδc d).noSL) (Icc 0 1) := by
  have hc0 := hP.c_nonneg
  have hc1 := hP.c_lt_one
  have hV := value_eq P hP
  refine ⟨hV, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hEq, hpr⟩ := opt_plan P hP
    exact ⟨_, hEq, by rw [hpr, hV]⟩
  · intro hδ p₁ p₂ ⟨B, hB, hpr⟩
    rw [hV, EReal.coe_eq_coe_iff] at hpr
    exact (main_bound P hP p₁ p₂ B hB).2 hδ hpr
  · intro a ha b hb hab
    simp only
    rw [div_lt_div_iff₀ (by linarith [hb.1]) (by linarith [ha.1])]
    nlinarith
  · intro a ha b hb hab
    simp only
    rw [div_lt_div_iff₀ (by linarith [ha.1]) (by linarith [hb.1])]
    nlinarith
  · intro a ha b hb hab
    have hSa : (P.withδc a).Standing :=
      ⟨hP.σp_pos, hP.γ_nonneg, ha.1, ha.2, hP.c_nonneg, hP.c_lt_one⟩
    have hSb : (P.withδc b).Standing :=
      ⟨hP.σp_pos, hP.γ_nonneg, hb.1, hb.2, hP.c_nonneg, hP.c_lt_one⟩
    simp only
    rw [value_eq _ hSa, value_eq _ hSb, EReal.coe_lt_coe_iff]
    show (1 - P.c) ^ 2 / (b + 3) < (1 - P.c) ^ 2 / (a + 3)
    exact div_lt_div_of_pos_left (by nlinarith) (by linarith [ha.1]) (by linarith)
