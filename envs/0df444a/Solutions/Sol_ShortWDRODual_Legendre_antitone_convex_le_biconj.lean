-- Prove2me | solution 1 for ShortWDRODual.Legendre.antitone_convex_le_biconj
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:55:47.777301+00:00
-- url     : https://prove2.me/submissions/30953b25-13b3-4bc7-9351-64e64ea00023

import Mathlib

namespace WDRO1Biconj

/-- Left three-slope inequality: `μ < l < a`, `l = (1-t) μ + t a`. -/
lemma three_slope_left {μ l a gμ g ga : ℝ} (h1 : μ < l) (h2 : l < a)
    (h : g ≤ (1 - (l - μ) / (a - μ)) * gμ + ((l - μ) / (a - μ)) * ga) :
    g + (g - ga) / (a - l) * (l - μ) ≤ gμ := by
  have ha : 0 < a - μ := by linarith
  have hal : 0 < a - l := by linarith
  have e1 : (1 - (l - μ) / (a - μ)) = (a - l) / (a - μ) := by field_simp; ring
  rw [e1] at h
  have h' : g * (a - μ) ≤ (a - l) * gμ + (l - μ) * ga := by
    have := mul_le_mul_of_nonneg_right h ha.le
    have e2 : ((a - l) / (a - μ) * gμ + (l - μ) / (a - μ) * ga) * (a - μ)
        = (a - l) * gμ + (l - μ) * ga := by field_simp
    linarith
  have e3 : (g - ga) / (a - l) * (l - μ) = (g - ga) * (l - μ) / (a - l) := by ring
  rw [e3, ← sub_nonneg]
  have : gμ - (g + (g - ga) * (l - μ) / (a - l)) = ((a - l) * gμ + (l - μ) * ga - g * (a - μ)) / (a - l) := by
    field_simp; ring
  rw [this]
  apply div_nonneg _ hal.le
  linarith

/-- Right three-slope inequality: `l < a < μ`, `a = (1-t) l + t μ`. -/
lemma three_slope_right {l a μ g ga gμ : ℝ} (h1 : l < a) (h2 : a < μ)
    (h : ga ≤ (1 - (a - l) / (μ - l)) * g + ((a - l) / (μ - l)) * gμ) :
    ga - (g - ga) / (a - l) * (μ - a) ≤ gμ := by
  have hm : 0 < μ - l := by linarith
  have hal : 0 < a - l := by linarith
  have e1 : (1 - (a - l) / (μ - l)) = (μ - a) / (μ - l) := by field_simp; ring
  rw [e1] at h
  have h' : ga * (μ - l) ≤ (μ - a) * g + (a - l) * gμ := by
    have := mul_le_mul_of_nonneg_right h hm.le
    have e2 : ((μ - a) / (μ - l) * g + (a - l) / (μ - l) * gμ) * (μ - l)
        = (μ - a) * g + (a - l) * gμ := by field_simp
    linarith
  rw [← sub_nonneg]
  have : gμ - (ga - (g - ga) / (a - l) * (μ - a)) = ((μ - a) * g + (a - l) * gμ - ga * (μ - l)) / (a - l) := by
    field_simp; ring
  rw [this]
  apply div_nonneg _ hal.le
  linarith

lemma coe_conv (t x z : ℝ) :
    ((1 - t : ℝ) : EReal) * (x : EReal) + ((t : ℝ) : EReal) * (z : EReal) =
      (((1 - t) * x + t * z : ℝ) : EReal) := by
  rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]

lemma real_of {e : EReal} (h1 : e ≠ ⊤) (h2 : e ≠ ⊥) : e = ((e.toReal : ℝ) : EReal) :=
  (EReal.coe_toReal h1 h2).symm

end WDRO1Biconj

open WDRO1Biconj

theorem solution (G : ℝ → EReal)
    (hbot : ∀ μ : ℝ, 0 ≤ μ → G μ ≠ ⊥)
    (hanti : AntitoneOn G (Set.Ici 0))
    (hconv : ∀ a b t : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ t → t ≤ 1 →
      G ((1 - t) * a + t * b) ≤ ((1 - t : ℝ) : EReal) * G a + ((t : ℝ) : EReal) * G b)
    (hlsc : LowerSemicontinuousOn G (Set.Ici 0))
    (lam : ℝ) (hlam : 0 < lam) :
    G lam ≤ ⨆ (ρ : ℝ) (_ : 0 < ρ),
      ((⨅ (μ : ℝ) (_ : 0 ≤ μ), ((μ * ρ : ℝ) : EReal) + G μ) - ((lam * ρ : ℝ) : EReal)) := by
  set R := ⨆ (ρ : ℝ) (_ : 0 < ρ),
      ((⨅ (μ : ℝ) (_ : 0 ≤ μ), ((μ * ρ : ℝ) : EReal) + G μ) - ((lam * ρ : ℝ) : EReal)) with hR
  -- reduction to the existence of an affine minorant
  have key_to_R : ∀ y : ℝ, (∃ ρ : ℝ, 0 < ρ ∧ ∀ μ : ℝ, 0 ≤ μ →
      ((y + ρ * (lam - μ) : ℝ) : EReal) ≤ G μ) → (y : EReal) ≤ R := by
    rintro y ⟨ρ, hρ, hmin⟩
    refine le_iSup₂_of_le ρ hρ ?_
    have hI : ((y + lam * ρ : ℝ) : EReal) ≤ ⨅ (μ : ℝ) (_ : 0 ≤ μ), ((μ * ρ : ℝ) : EReal) + G μ := by
      refine le_iInf₂ fun μ hμ => ?_
      have e : ((y + lam * ρ : ℝ) : EReal) = ((μ * ρ : ℝ) : EReal) + ((y + ρ * (lam - μ) : ℝ) : EReal) := by
        rw [← EReal.coe_add]; congr 1; ring
      rw [e]
      exact add_le_add le_rfl (hmin μ hμ)
    have := EReal.sub_le_sub hI (le_refl ((lam * ρ : ℝ) : EReal))
    rw [← EReal.coe_sub, add_sub_cancel_right] at this
    exact this
  -- lower semicontinuity in metric form
  have hlsc' : ∀ y : ℝ, (y : EReal) < G lam → ∃ δ > 0, ∀ μ : ℝ, 0 ≤ μ → |μ - lam| < δ →
      (y : EReal) < G μ := by
    intro y hy
    have h := hlsc lam (Set.mem_Ici.mpr hlam.le) (y : EReal) hy
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨δ, hδ, hball⟩ := h
    exact ⟨δ, hδ, fun μ hμ hd => hball (by rw [Real.dist_eq]; exact hd) (Set.mem_Ici.mpr hμ)⟩
  have key : ∀ y : ℝ, (y : EReal) < G lam → ∃ ρ : ℝ, 0 < ρ ∧ ∀ μ : ℝ, 0 ≤ μ →
      ((y + ρ * (lam - μ) : ℝ) : EReal) ≤ G μ := by
    intro y hy
    obtain ⟨δ, hδ, hnear⟩ := hlsc' y hy
    by_cases htop : G lam = ⊤
    · -- Case A: `G λ = ⊤`
      by_cases hall : ∀ μ : ℝ, 0 ≤ μ → G μ = ⊤
      · exact ⟨1, one_pos, fun μ hμ => by rw [hall μ hμ]; exact le_top⟩
      push_neg at hall
      obtain ⟨p, hp0, hpt⟩ := hall
      have hplam : lam < p := by
        by_contra hle
        push_neg at hle
        have := hanti (Set.mem_Ici.mpr hp0) (Set.mem_Ici.mpr hlam.le) hle
        rw [htop, top_le_iff] at this
        exact hpt this
      set q := p + 1 with hq
      have hq0 : 0 ≤ q := by linarith
      have hGqp : G q ≤ G p := hanti (Set.mem_Ici.mpr hp0) (Set.mem_Ici.mpr hq0) (by linarith)
      have hqt : G q ≠ ⊤ := ne_top_of_le_ne_top hpt hGqp
      set gp := (G p).toReal
      set gq := (G q).toReal
      have hGp : G p = (gp : EReal) := real_of hpt (hbot p hp0)
      have hGq : G q = (gq : EReal) := real_of hqt (hbot q hq0)
      set s := gp - gq with hs
      have hs0 : 0 ≤ s := by
        have : (gq : EReal) ≤ (gp : EReal) := by rw [← hGp, ← hGq]; exact hGqp
        have : gq ≤ gp := by exact_mod_cast this
        linarith
      set K := (|y - gq| + 1) / δ with hK
      have hK0 : 0 < K := by positivity
      refine ⟨s + K, by linarith, fun μ hμ => ?_⟩
      by_cases hμl : μ ≤ lam
      · have := hanti (Set.mem_Ici.mpr hμ) (Set.mem_Ici.mpr hlam.le) hμl
        rw [htop, top_le_iff] at this
        rw [this]; exact le_top
      push_neg at hμl
      by_cases hμd : μ < lam + δ
      · have h1 := hnear μ hμ (by rw [abs_lt]; constructor <;> linarith)
        refine le_of_lt (lt_of_le_of_lt ?_ h1)
        have : (s + K) * (lam - μ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
        exact_mod_cast (by linarith : y + (s + K) * (lam - μ) ≤ y)
      push_neg at hμd
      have hKd : K * (μ - lam) ≥ |y - gq| + 1 := by
        rw [hK, div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hδ]
        have : 0 ≤ |y - gq| + 1 := by positivity
        nlinarith
      have hy_gq : y - gq ≤ |y - gq| := le_abs_self _
      by_cases hμq : μ ≤ q
      · have hGμq : G q ≤ G μ := hanti (Set.mem_Ici.mpr hμ) (Set.mem_Ici.mpr hq0) hμq
        refine le_trans ?_ (hGq ▸ hGμq)
        have : s * (μ - lam) ≥ 0 := mul_nonneg hs0 (by linarith)
        exact_mod_cast (by nlinarith : y + (s + K) * (lam - μ) ≤ gq)
      · push_neg at hμq
        have hGμq : G μ ≤ G q := hanti (Set.mem_Ici.mpr hq0) (Set.mem_Ici.mpr hμ) hμq.le
        have hμt : G μ ≠ ⊤ := ne_top_of_le_ne_top hqt hGμq
        set gμ := (G μ).toReal
        have hGμ : G μ = (gμ : EReal) := real_of hμt (hbot μ hμ)
        set t := (q - p) / (μ - p) with ht
        have hpμ : 0 < μ - p := by linarith
        have ht0 : 0 ≤ t := div_nonneg (by linarith) hpμ.le
        have ht1 : t ≤ 1 := by rw [ht, div_le_one hpμ]; linarith
        have hpt' : (1 - t) * p + t * μ = q := by
          rw [ht]; field_simp; ring
        have hc := hconv p μ t hp0 hμ ht0 ht1
        rw [hpt', hGp, hGμ, hGq, coe_conv] at hc
        have hc' : gq ≤ (1 - (q - p) / (μ - p)) * gp + ((q - p) / (μ - p)) * gμ := by
          exact_mod_cast hc
        have h3 := three_slope_right (l := p) (a := q) (μ := μ) (by linarith) hμq hc'
        have hqp : q - p = 1 := by rw [hq]; ring
        rw [hqp, div_one] at h3
        rw [hGμ]
        have : s * (μ - lam) ≥ s * (μ - q) := by
          apply mul_le_mul_of_nonneg_left _ hs0; linarith
        exact_mod_cast (by nlinarith : y + (s + K) * (lam - μ) ≤ gμ)
    · -- Case B: `G λ` finite
      set g := (G lam).toReal
      have hGl : G lam = (g : EReal) := real_of htop (hbot lam hlam.le)
      have hyg : y < g := by have := hy; rw [hGl] at this; exact_mod_cast this
      set a := lam + δ / 2 with ha
      have ha0 : 0 ≤ a := by positivity
      have hla : lam < a := by linarith
      have hGa_le : G a ≤ G lam := hanti (Set.mem_Ici.mpr hlam.le) (Set.mem_Ici.mpr ha0) hla.le
      have hat : G a ≠ ⊤ := ne_top_of_le_ne_top htop hGa_le
      set ga := (G a).toReal
      have hGa : G a = (ga : EReal) := real_of hat (hbot a ha0)
      have hga_g : ga ≤ g := by
        have : (ga : EReal) ≤ (g : EReal) := by rw [← hGa, ← hGl]; exact hGa_le
        exact_mod_cast this
      have hyga : y < ga := by
        have := hnear a ha0 (by rw [abs_lt]; constructor <;> linarith)
        rw [hGa] at this; exact_mod_cast this
      set sR := (g - ga) / (a - lam) with hsR
      have hsR0 : 0 ≤ sR := div_nonneg (by linarith) (by linarith)
      set K := (g - y) / lam with hK
      have hK0 : 0 < K := div_pos (by linarith) hlam
      refine ⟨sR + K, by linarith, fun μ hμ => ?_⟩
      rcases lt_or_ge μ lam with hμl | hμl
      · by_cases hμt : G μ = ⊤
        · rw [hμt]; exact le_top
        set gμ := (G μ).toReal
        have hGμ : G μ = (gμ : EReal) := real_of hμt (hbot μ hμ)
        set t := (lam - μ) / (a - μ) with ht
        have haμ : 0 < a - μ := by linarith
        have ht0 : 0 ≤ t := div_nonneg (by linarith) haμ.le
        have ht1 : t ≤ 1 := by rw [ht, div_le_one haμ]; linarith
        have hpt' : (1 - t) * μ + t * a = lam := by
          rw [ht]; field_simp; ring
        have hc := hconv μ a t hμ ha0 ht0 ht1
        rw [hpt', hGμ, hGa, hGl, coe_conv] at hc
        have hc' : g ≤ (1 - (lam - μ) / (a - μ)) * gμ + ((lam - μ) / (a - μ)) * ga := by
          exact_mod_cast hc
        have h3 := three_slope_left hμl hla hc'
        rw [hGμ]
        have hKl : K * (lam - μ) ≤ g - y := by
          rw [hK, div_mul_eq_mul_div, div_le_iff₀ hlam]
          nlinarith
        exact_mod_cast (by nlinarith : y + (sR + K) * (lam - μ) ≤ gμ)
      · by_cases hμa : μ ≤ a
        · have h1 := hnear μ hμ (by rw [abs_lt]; constructor <;> linarith)
          refine le_of_lt (lt_of_le_of_lt ?_ h1)
          have : (sR + K) * (lam - μ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
          exact_mod_cast (by linarith : y + (sR + K) * (lam - μ) ≤ y)
        · push_neg at hμa
          have hGμa : G μ ≤ G a := hanti (Set.mem_Ici.mpr ha0) (Set.mem_Ici.mpr hμ) hμa.le
          have hμt : G μ ≠ ⊤ := ne_top_of_le_ne_top hat hGμa
          set gμ := (G μ).toReal
          have hGμ : G μ = (gμ : EReal) := real_of hμt (hbot μ hμ)
          set t := (a - lam) / (μ - lam) with ht
          have hμl' : 0 < μ - lam := by linarith
          have ht0 : 0 ≤ t := div_nonneg (by linarith) hμl'.le
          have ht1 : t ≤ 1 := by rw [ht, div_le_one hμl']; linarith
          have hpt' : (1 - t) * lam + t * μ = a := by
            rw [ht]; field_simp; ring
          have hc := hconv lam μ t hlam.le hμ ht0 ht1
          rw [hpt', hGμ, hGa, hGl, coe_conv] at hc
          have hc' : ga ≤ (1 - (a - lam) / (μ - lam)) * g + ((a - lam) / (μ - lam)) * gμ := by
            exact_mod_cast hc
          have h3 := three_slope_right hla hμa hc'
          rw [hGμ]
          have h4 : sR * (μ - lam) ≥ sR * (μ - a) := by
            apply mul_le_mul_of_nonneg_left _ hsR0; linarith
          have h5 : K * (μ - lam) ≥ 0 := mul_nonneg hK0.le (by linarith)
          exact_mod_cast (by nlinarith : y + (sR + K) * (lam - μ) ≤ gμ)
  -- conclude
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy1, hy2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
  exact absurd (key_to_R y (key y hy2)) (not_le.mpr hy1)
-- 
