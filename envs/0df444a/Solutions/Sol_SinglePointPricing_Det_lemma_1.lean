-- Prove2me | solution 1 for SinglePointPricing.Det.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:47:56.344858+00:00
-- url     : https://prove2.me/submissions/eb3f7671-73cf-43b0-812e-99d094a2f325

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase

open SinglePointPricing.Det MeasureTheory

lemma hGA_pos (α x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) : 0 < GammaA α x := by
  unfold GammaA
  split_ifs with h
  · exact Real.exp_pos _
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply Real.rpow_pos_of_pos; nlinarith

lemma hGA_zero (α : ℝ) : GammaA α 0 = 1 := by
  unfold GammaA; split_ifs <;> simp

lemma hGAInv_one (α : ℝ) : GammaAInv α 1 = 0 := by
  unfold GammaAInv; split_ifs <;> simp

lemma hGAInv_GA (α x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    GammaAInv α (GammaA α x) = x := by
  unfold GammaA GammaAInv
  split_ifs with h
  · simp
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    have hb : 0 ≤ 1 + (1 - α) * x := by nlinarith
    rw [← Real.rpow_mul hb]
    have : -(1 / (1 - α)) * -(1 - α) = 1 := by field_simp
    rw [this, Real.rpow_one]; field_simp; ring

lemma hGA_GAInv (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : 0 < q) :
    GammaA α (GammaAInv α q) = q := by
  unfold GammaA GammaAInv
  split_ifs with h
  · simp [Real.exp_log hq]
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    have : 1 + (1 - α) * ((q ^ (-(1 - α)) - 1) / (1 - α)) = q ^ (-(1 - α)) := by
      field_simp; ring
    rw [this, ← Real.rpow_mul hq.le]
    have : -(1 - α) * -(1 / (1 - α)) = 1 := by field_simp
    rw [this, Real.rpow_one]

lemma hGAInv_pos (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    0 < GammaAInv α q := by
  rcases hq with ⟨h0, h1⟩
  unfold GammaAInv
  split_ifs with h
  · have := Real.log_neg h0 h1; linarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply div_pos _ ha
    have : 1 < q ^ (-(1 - α)) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg h0 h1 (by linarith)
    linarith

/-- strict antitonicity of GammaAInv on (0, ∞) -/
lemma hGAInv_anti (α x y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 < x) (hxy : x < y) :
    GammaAInv α y < GammaAInv α x := by
  unfold GammaAInv
  split_ifs with h
  · have := Real.log_lt_log hx hxy; linarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply div_lt_div_of_pos_right _ ha
    have := Real.rpow_lt_rpow_of_neg hx hxy (by linarith : -(1 - α) < 0)
    linarith

lemma hGA_anti (α x y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) (hxy : x ≤ y) :
    GammaA α y ≤ GammaA α x := by
  unfold GammaA
  split_ifs with h
  · exact Real.exp_le_exp.mpr (by linarith)
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply Real.rpow_le_rpow_of_nonpos (by nlinarith) (by nlinarith)
    have : 0 < 1 / (1 - α) := by positivity
    linarith

lemma interp_id (α qs qs' τ : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hqs : 0 < qs) (hqs' : 0 < qs')
    (hle : qs' ≤ qs) (hτ : 0 ≤ τ) :
    GammaAInv α (qs * GammaA α (GammaAInv α (qs' / qs) * τ)) =
      (1 - τ) * GammaAInv α qs + τ * GammaAInv α qs' := by
  have hk : 0 ≤ GammaAInv α (qs' / qs) := by
    rcases eq_or_lt_of_le hle with h | h
    · rw [h, div_self hqs.ne', hGAInv_one]
    · have := hGAInv_anti α (qs' / qs) 1 hα (div_pos hqs' hqs) ((div_lt_one hqs).mpr h)
      rw [hGAInv_one] at this; linarith
  unfold GammaA GammaAInv
  split_ifs with h
  · rw [Real.log_mul hqs.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_div hqs'.ne' hqs.ne']
    ring
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    set a := 1 - α with ha_def
    have hb : 0 ≤ 1 + a * ((qs' / qs) ^ (-a) - 1) / a * τ := by
      have h1 : 1 ≤ (qs' / qs) ^ (-a) := by
        apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos (div_pos hqs' hqs)
          ((div_le_one hqs).mpr hle) (by linarith)
      have e : a * ((qs' / qs) ^ (-a) - 1) / a * τ = ((qs' / qs) ^ (-a) - 1) * τ := by
        field_simp
      rw [e]
      have : 0 ≤ ((qs' / qs) ^ (-a) - 1) * τ := mul_nonneg (by linarith) hτ
      linarith
    have hb' : 1 + a * (((qs' / qs) ^ (-a) - 1) / a * τ) = 1 + a * ((qs' / qs) ^ (-a) - 1) / a * τ := by ring
    rw [hb', Real.mul_rpow hqs.le (Real.rpow_nonneg hb _), ← Real.rpow_mul hb]
    have : -(1 / a) * -a = 1 := by field_simp
    rw [this, Real.rpow_one, Real.div_rpow hqs'.le hqs.le]
    have hp : 0 < qs ^ (-a) := Real.rpow_pos_of_pos hqs _
    field_simp
    ring

theorem solution (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hSR : IsAlphaSR α μ) (s s' : ℝ) (hs : 0 ≤ s) (hss' : s ≤ s')
    (hq : 0 < sf μ s') :
    (∀ v ∈ Set.Icc s s',
      sf μ s * GammaA α (GammaAInv α (sf μ s' / sf μ s) * (v - s) / (s' - s)) ≤ sf μ v) ∧
    (∀ v ∈ Set.Ioi s',
      sf μ v ≤ sf μ s * GammaA α (GammaAInv α (sf μ s' / sf μ s) * (v - s) / (s' - s))) := by
  have hanti : ∀ x y, x ≤ y → sf μ y ≤ sf μ x := by
    intro x y hxy
    unfold sf
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.Ici_subset_Ici.mpr hxy))
  have hnn : ∀ x, 0 ≤ sf μ x := fun x => ENNReal.toReal_nonneg
  have hqs : 0 < sf μ s := lt_of_lt_of_le hq (hanti _ _ hss')
  have hle : sf μ s' ≤ sf μ s := hanti _ _ hss'
  rcases eq_or_lt_of_le hss' with heq | hlt
  · subst heq
    simp only [sub_self, div_zero, hGA_zero, mul_one]
    refine ⟨?_, ?_⟩
    · intro v hv
      have : v = s := le_antisymm hv.2 hv.1
      rw [this]
    · intro v hv; exact hanti _ _ (le_of_lt hv)
  have hd : 0 < s' - s := sub_pos.mpr hlt
  set φ := fun v => GammaAInv α (sf μ v) with hφ
  have key : ∀ v, s ≤ v →
      GammaAInv α (sf μ s * GammaA α (GammaAInv α (sf μ s' / sf μ s) * (v - s) / (s' - s))) =
        (1 - (v - s) / (s' - s)) * φ s + (v - s) / (s' - s) * φ s' := by
    intro v hv
    rw [mul_div_assoc]
    exact interp_id α _ _ _ hα hqs hq hle (div_nonneg (by linarith) hd.le)
  have Ipos : ∀ v, s ≤ v →
      0 < sf μ s * GammaA α (GammaAInv α (sf μ s' / sf μ s) * (v - s) / (s' - s)) := by
    intro v hv
    have hk : 0 ≤ GammaAInv α (sf μ s' / sf μ s) := by
      rcases eq_or_lt_of_le hle with h | h
      · rw [h, div_self hqs.ne', hGAInv_one]
      · have := hGAInv_anti α _ 1 hα (div_pos hq hqs) ((div_lt_one hqs).mpr h)
        rw [hGAInv_one] at this; linarith
    exact mul_pos hqs (hGA_pos α _ hα (div_nonneg (mul_nonneg hk (by linarith)) hd.le))
  have hsD : s ∈ {v : ℝ | 0 ≤ v ∧ 0 < sf μ v} := ⟨hs, hqs⟩
  have hs'D : s' ∈ {v : ℝ | 0 ≤ v ∧ 0 < sf μ v} := ⟨by linarith, hq⟩
  refine ⟨?_, ?_⟩
  · intro v hv
    have hvpos : 0 < sf μ v := lt_of_lt_of_le hq (hanti _ _ hv.2)
    by_contra hcon
    push_neg at hcon
    have h1 := hGAInv_anti α _ _ hα hvpos hcon
    rw [key v hv.1] at h1
    -- convexity
    set τ := (v - s) / (s' - s) with hτ
    have hτ0 : 0 ≤ τ := div_nonneg (by linarith [hv.1]) hd.le
    have hτ1 : τ ≤ 1 := (div_le_one hd).mpr (by linarith [hv.2])
    have hc := hSR.2 hsD hs'D (sub_nonneg.mpr hτ1) hτ0 (by ring)
    have hv_eq : (1 - τ) • s + τ • s' = v := by
      simp only [smul_eq_mul]; rw [hτ]; field_simp; ring
    rw [hv_eq] at hc
    simp only [smul_eq_mul] at hc
    have : φ v = GammaAInv α (sf μ v) := rfl
    linarith
  · intro v hv
    have hv' : s' < v := hv
    rcases eq_or_lt_of_le (hnn v) with h0 | hvpos
    · rw [← h0]; exact (Ipos v (by linarith)).le
    by_contra hcon
    push_neg at hcon
    have h1 := hGAInv_anti α _ _ hα (Ipos v (by linarith)) hcon
    rw [key v (by linarith)] at h1
    have hvD : v ∈ {v : ℝ | 0 ≤ v ∧ 0 < sf μ v} := ⟨by linarith, hvpos⟩
    have hdv : 0 < v - s := by linarith
    set l := (s' - s) / (v - s) with hl
    have hl0 : 0 ≤ l := div_nonneg hd.le hdv.le
    have hl1 : l ≤ 1 := (div_le_one hdv).mpr (by linarith)
    have hc := hSR.2 hsD hvD (sub_nonneg.mpr hl1) hl0 (by ring)
    have hv_eq : (1 - l) • s + l • v = s' := by
      simp only [smul_eq_mul]; rw [hl]; field_simp; ring
    rw [hv_eq] at hc
    simp only [smul_eq_mul] at hc
    -- hc : φ s' ≤ (1 - l) * φ s + l * φ v
    have hlpos : 0 < l := div_pos hd hdv
    have hτl : (v - s) / (s' - s) * l = 1 := by rw [hl]; field_simp
    have : φ v = GammaAInv α (sf μ v) := rfl
    have hfin : (1 - (v - s) / (s' - s)) * φ s + (v - s) / (s' - s) * φ s' ≤ φ v := by
      have hτ0 : 0 ≤ (v - s) / (s' - s) := div_nonneg hdv.le hd.le
      have := mul_le_mul_of_nonneg_left hc hτ0
      have e : (v - s) / (s' - s) * ((1 - l) * φ s + l * φ v)
          = (v - s) / (s' - s) * φ s - φ s + φ v := by
        linear_combination (φ v - φ s) * hτl
      linarith
    linarith
