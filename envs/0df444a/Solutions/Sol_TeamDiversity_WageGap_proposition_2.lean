-- Prove2me | solution 1 for TeamDiversity.WageGap.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T04:35:42.260531+00:00
-- url     : https://prove2.me/submissions/ca78b87b-cb6b-45e0-9e0c-59d69a891404

import Mathlib
import Definitions.Def_TeamDiversity_WageGap_Model

open TeamDiversity.WageGap

namespace WGSol

lemma nonneg_of_mul_pos {x u : ℝ} (hu : 0 < u) (h : 0 ≤ x * u) : 0 ≤ x := by
  by_contra hx
  push Not at hx
  nlinarith [mul_neg_of_neg_of_pos hx hu]

lemma wd_formula (c : ℝ) (fd : Tech) (hc : 0 < c) (hb0 : 0 < fd.f0) (hb01 : fd.f0 < fd.f1)
    (hb12 : fd.f1 < fd.f2) (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (w : ℝ)
    (h : IsLeast (FeasD c fd δ) w) :
    w = c / ((fd.f2 - fd.f1) + δ * (fd.f1 - fd.f0)) := by
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hD : 0 < (fd.f2 - fd.f1) + δ * (fd.f1 - fd.f0) := by nlinarith
  have hW : c / ((fd.f2 - fd.f1) + δ * (fd.f1 - fd.f0)) *
      ((fd.f2 - fd.f1) + δ * (fd.f1 - fd.f0)) = c := div_mul_cancel₀ c hD.ne'
  have hW0 : 0 ≤ c / ((fd.f2 - fd.f1) + δ * (fd.f1 - fd.f0)) := div_nonneg hc.le hD.le
  refine h.unique ⟨?_, ?_⟩
  · simp only [FeasD, Set.mem_setOf_eq]
    refine ⟨hW0, ?_, ?_⟩
    · have : 0 ≤ (1 - δ) * fd.f1 + δ * fd.f0 := by nlinarith
      nlinarith [mul_nonneg hW0 this]
    · linarith
  · intro x hx
    simp only [FeasD, Set.mem_setOf_eq] at hx
    obtain ⟨_, _, hm⟩ := hx
    rw [div_le_iff₀ hD]
    linarith

/-- Region δ < δ^m. -/
lemma ws_formula1 (c : ℝ) (fs : Tech) (hc : 0 < c) (ha0 : 0 < fs.f0) (ha01 : fs.f0 < fs.f1)
    (ha12 : fs.f1 < fs.f2) (hA2 : fs.f1 - fs.f0 < 2 * (fs.f2 - fs.f1))
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hlt : δ < deltaM fs) (w : ℝ)
    (h : IsLeast (FeasS c fs δ) w) :
    w = c * (1 - δ) / (fs.f2 - fs.f1) := by
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hu : 0 < fs.f2 - fs.f1 := by linarith
  have hv : 0 < fs.f1 - fs.f0 := by linarith
  have hlt' : δ * (fs.f1 - fs.f0) < 2 * fs.f1 - fs.f2 - fs.f0 := by
    unfold deltaM at hlt; rwa [lt_div_iff₀ hv] at hlt
  have hδhalf : δ < 1 / 2 := by nlinarith
  have hW : c * (1 - δ) / (fs.f2 - fs.f1) * (fs.f2 - fs.f1) = c * (1 - δ) :=
    div_mul_cancel₀ _ hu.ne'
  have hW0 : 0 ≤ c * (1 - δ) / (fs.f2 - fs.f1) := div_nonneg (by nlinarith) hu.le
  have hnle : ¬ deltaM fs ≤ δ := not_le.mpr hlt
  refine h.unique ⟨?_, ?_⟩
  · simp only [FeasS, FeasSMM, Set.mem_setOf_eq]
    refine ⟨⟨hW0, ?_, ?_⟩, ?_⟩
    · rw [ge_iff_le, ← sub_nonneg, sub_zero]
      apply nonneg_of_mul_pos hu
      have e : (fs.f2 * (c * (1 - δ) / (fs.f2 - fs.f1)) - c) * (fs.f2 - fs.f1)
          = c * (fs.f2 * (1 - δ) - (fs.f2 - fs.f1)) := by linear_combination fs.f2 * hW
      rw [e]
      apply mul_nonneg hc.le
      nlinarith
    · unfold MICs; rw [if_neg hnle]; linarith
    · unfold NoCycling
      rw [← add_div, ge_iff_le, div_le_iff₀ (by linarith)]
      have e : (fs.f2 * (c * (1 - δ) / (fs.f2 - fs.f1)) - c) * (1 + δ) -
          ((fs.f1 * (c * (1 - δ) / (fs.f2 - fs.f1)) - c) +
            δ * (fs.f1 * (c * (1 - δ) / (fs.f2 - fs.f1)))) = c * (1 - δ - δ ^ 2) := by
        linear_combination (1 + δ) * hW
      have : 0 ≤ c * (1 - δ - δ ^ 2) := mul_nonneg hc.le (by nlinarith)
      linarith
  · intro x hx
    simp only [FeasS, FeasSMM, Set.mem_setOf_eq] at hx
    obtain ⟨⟨_, _, hm⟩, _⟩ := hx
    unfold MICs at hm; rw [if_neg hnle] at hm
    rw [div_le_iff₀ hu]
    linarith

/-- Region δ^m ≤ δ ≤ δ^C. -/
lemma ws_formula2 (c : ℝ) (fs : Tech) (hc : 0 < c) (ha0 : 0 < fs.f0) (ha01 : fs.f0 < fs.f1)
    (ha12 : fs.f1 < fs.f2)
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hle : deltaM fs ≤ δ) (hC : δ ≤ deltaC fs) (w : ℝ)
    (h : IsLeast (FeasS c fs δ) w) :
    w = c / ((fs.f2 - fs.f1) + δ * (fs.f1 - fs.f0)) := by
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hu : 0 < fs.f2 - fs.f1 := by linarith
  have hv : 0 < fs.f1 - fs.f0 := by linarith
  have hsq : δ ^ 2 * (fs.f1 - fs.f0) ≤ fs.f2 - fs.f1 := by
    unfold deltaC at hC
    have := (Real.le_sqrt hδ0 (div_nonneg hu.le hv.le)).mp hC
    rwa [le_div_iff₀ hv] at this
  have hD : 0 < (fs.f2 - fs.f1) + δ * (fs.f1 - fs.f0) := by nlinarith
  have hW : c / ((fs.f2 - fs.f1) + δ * (fs.f1 - fs.f0)) *
      ((fs.f2 - fs.f1) + δ * (fs.f1 - fs.f0)) = c := div_mul_cancel₀ c hD.ne'
  have hW0 : 0 ≤ c / ((fs.f2 - fs.f1) + δ * (fs.f1 - fs.f0)) := div_nonneg hc.le hD.le
  refine h.unique ⟨?_, ?_⟩
  · simp only [FeasS, FeasSMM, Set.mem_setOf_eq]
    refine ⟨⟨hW0, ?_, ?_⟩, ?_⟩
    · have : 0 ≤ (1 - δ) * fs.f1 + δ * fs.f0 := by nlinarith
      nlinarith [mul_nonneg hW0 this]
    · unfold MICs; rw [if_pos hle]; linarith
    · unfold NoCycling
      rw [← add_div, ge_iff_le, div_le_iff₀ (by linarith)]
      apply sub_nonneg.mp
      apply nonneg_of_mul_pos hD
      have e : ((fs.f2 * (c / ((fs.f2 - fs.f1) + δ * (fs.f1 - fs.f0))) - c) * (1 + δ) -
          ((fs.f1 * (c / ((fs.f2 - fs.f1) + δ * (fs.f1 - fs.f0))) - c) +
            δ * (fs.f1 * (c / ((fs.f2 - fs.f1) + δ * (fs.f1 - fs.f0)))))) *
            ((fs.f2 - fs.f1) + δ * (fs.f1 - fs.f0)) =
          c * ((fs.f2 - fs.f1) - δ ^ 2 * (fs.f1 - fs.f0)) := by
        linear_combination (1 + δ) * (fs.f2 - fs.f1) * hW
      rw [e]
      exact mul_nonneg hc.le (by linarith)
  · intro x hx
    simp only [FeasS, FeasSMM, Set.mem_setOf_eq] at hx
    obtain ⟨⟨_, _, hm⟩, _⟩ := hx
    unfold MICs at hm; rw [if_pos hle] at hm
    rw [div_le_iff₀ hD]
    linarith

/-- Region δ^C < δ (given δ^m ≤ δ). -/
lemma ws_formula3 (c : ℝ) (fs : Tech) (hc : 0 < c) (ha0 : 0 < fs.f0) (ha01 : fs.f0 < fs.f1)
    (ha12 : fs.f1 < fs.f2)
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hle : deltaM fs ≤ δ) (hC : deltaC fs < δ) (w : ℝ)
    (h : IsLeast (FeasS c fs δ) w) :
    w = c * δ / ((1 + δ) * (fs.f2 - fs.f1)) := by
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hu : 0 < fs.f2 - fs.f1 := by linarith
  have hv : 0 < fs.f1 - fs.f0 := by linarith
  have hδpos : 0 < δ := lt_of_le_of_lt (Real.sqrt_nonneg _) hC
  have hsq : fs.f2 - fs.f1 < δ ^ 2 * (fs.f1 - fs.f0) := by
    unfold deltaC at hC
    have := (Real.sqrt_lt' hδpos).mp hC
    rwa [div_lt_iff₀ hv] at this
  have hD : 0 < (1 + δ) * (fs.f2 - fs.f1) := by positivity
  have hW : c * δ / ((1 + δ) * (fs.f2 - fs.f1)) * ((1 + δ) * (fs.f2 - fs.f1)) = c * δ :=
    div_mul_cancel₀ _ hD.ne'
  have hW0 : 0 ≤ c * δ / ((1 + δ) * (fs.f2 - fs.f1)) := div_nonneg (by positivity) hD.le
  have hmic : (fs.f2 - fs.f1 + δ * (fs.f1 - fs.f0)) * (c * δ / ((1 + δ) * (fs.f2 - fs.f1))) - c
      ≥ 0 := by
    apply nonneg_of_mul_pos hD
    have e : ((fs.f2 - fs.f1 + δ * (fs.f1 - fs.f0)) * (c * δ / ((1 + δ) * (fs.f2 - fs.f1))) - c)
        * ((1 + δ) * (fs.f2 - fs.f1)) = c * (δ ^ 2 * (fs.f1 - fs.f0) - (fs.f2 - fs.f1)) := by
      linear_combination (fs.f2 - fs.f1 + δ * (fs.f1 - fs.f0)) * hW
    rw [e]; exact mul_nonneg hc.le (by linarith)
  refine h.unique ⟨?_, ?_⟩
  · simp only [FeasS, FeasSMM, Set.mem_setOf_eq]
    refine ⟨⟨hW0, ?_, ?_⟩, ?_⟩
    · have : 0 ≤ (1 - δ) * fs.f1 + δ * fs.f0 := by nlinarith
      nlinarith [mul_nonneg hW0 this]
    · unfold MICs; rw [if_pos hle]; linarith
    · unfold NoCycling
      rw [← add_div, ge_iff_le, div_le_iff₀ (by linarith)]
      linarith
  · intro x hx
    simp only [FeasS, FeasSMM, Set.mem_setOf_eq] at hx
    obtain ⟨_, hn⟩ := hx
    unfold NoCycling at hn
    rw [← add_div, ge_iff_le, div_le_iff₀ (by linarith)] at hn
    rw [div_le_iff₀ hD]
    linarith


lemma P1_anti (a1 a2 b0 b1 b2 c x y : ℝ) (hc : 0 < c) (ha12 : a1 < a2) (ha2 : 0 < a2) (hb0 : 0 < b0)
    (hb01 : b0 < b1) (hb12 : b1 < b2) (hd : b1 - b0 < b2 - b1)
    (h3 : b2 * (a2 - a1) < a2 * (b2 - b1)) (hx : 0 ≤ x) (hxy : x < y) :
    a2 * (c * (1 - y) / (a2 - a1)) - b2 * (c / ((b2 - b1) + y * (b1 - b0))) <
      a2 * (c * (1 - x) / (a2 - a1)) - b2 * (c / ((b2 - b1) + x * (b1 - b0))) := by
  have hu : 0 < a2 - a1 := by linarith
  have hDx : 0 < (b2 - b1) + x * (b1 - b0) := by nlinarith
  have hDy : 0 < (b2 - b1) + y * (b1 - b0) := by nlinarith
  have hDx' := hDx.ne'
  have hDy' := hDy.ne'
  have hu' := hu.ne'
  have e1 : a2 * (c * (1 - x) / (a2 - a1)) - a2 * (c * (1 - y) / (a2 - a1)) =
      a2 * c * (y - x) / (a2 - a1) := by field_simp; ring
  have e2 : b2 * (c / ((b2 - b1) + x * (b1 - b0))) - b2 * (c / ((b2 - b1) + y * (b1 - b0))) =
      b2 * c * (b1 - b0) * (y - x) / (((b2 - b1) + x * (b1 - b0)) * ((b2 - b1) + y * (b1 - b0))) := by
    rw [eq_div_iff (mul_ne_zero hDx' hDy')]
    have q1 : c / ((b2 - b1) + x * (b1 - b0)) * ((b2 - b1) + x * (b1 - b0)) = c := div_mul_cancel₀ _ hDx'
    have q2 : c / ((b2 - b1) + y * (b1 - b0)) * ((b2 - b1) + y * (b1 - b0)) = c := div_mul_cancel₀ _ hDy'
    linear_combination (b2 * ((b2 - b1) + y * (b1 - b0))) * q1 - (b2 * ((b2 - b1) + x * (b1 - b0))) * q2
  have key : b2 * c * (b1 - b0) * (y - x) /
      (((b2 - b1) + x * (b1 - b0)) * ((b2 - b1) + y * (b1 - b0))) < a2 * c * (y - x) / (a2 - a1) := by
    rw [div_lt_div_iff₀ (mul_pos hDx hDy) hu]
    have h1 : b2 * (a2 - a1) < a2 * ((b2 - b1) + y * (b1 - b0)) := by
      nlinarith [mul_nonneg (mul_nonneg ha2.le (show (0:ℝ) ≤ y by linarith)) (show (0:ℝ) ≤ b1 - b0 by linarith)]
    have h2 : (b1 - b0) < (b2 - b1) + x * (b1 - b0) := by nlinarith
    have h4 : b2 * (a2 - a1) * (b1 - b0) < a2 * ((b2 - b1) + y * (b1 - b0)) *
        ((b2 - b1) + x * (b1 - b0)) := mul_lt_mul'' h1 h2 (by nlinarith) (by linarith)
    have hcyx : 0 < c * (y - x) := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left h4 hcyx]
  linarith

lemma P2_anti (a0 a1 a2 b0 b1 b2 c x y : ℝ) (hc : 0 < c) (ha0 : 0 < a0) (ha01 : a0 < a1)
    (ha12 : a1 < a2) (hb0 : 0 < b0)
    (hb01 : b0 < b1) (hb12 : b1 < b2) (hs : a2 - a1 < a1 - a0) (hd : b1 - b0 < b2 - b1)
    (h3 : b2 * (a2 - a1) < a2 * (b2 - b1)) (hr : b0 * a2 < a0 * b2) (hx : 0 ≤ x) (hxy : x < y)
    (hy1 : y < 1) :
    a2 * (c / ((a2 - a1) + y * (a1 - a0))) - b2 * (c / ((b2 - b1) + y * (b1 - b0))) <
      a2 * (c / ((a2 - a1) + x * (a1 - a0))) - b2 * (c / ((b2 - b1) + x * (b1 - b0))) := by
  have hDx : 0 < (b2 - b1) + x * (b1 - b0) := by nlinarith
  have hDy : 0 < (b2 - b1) + y * (b1 - b0) := by nlinarith
  have hEx : 0 < (a2 - a1) + x * (a1 - a0) := by nlinarith
  have hEy : 0 < (a2 - a1) + y * (a1 - a0) := by nlinarith
  have hDx' := hDx.ne'
  have hDy' := hDy.ne'
  have hEx' := hEx.ne'
  have hEy' := hEy.ne'
  have e1 : a2 * (c / ((a2 - a1) + x * (a1 - a0))) - a2 * (c / ((a2 - a1) + y * (a1 - a0))) =
      a2 * c * (a1 - a0) * (y - x) / (((a2 - a1) + x * (a1 - a0)) * ((a2 - a1) + y * (a1 - a0))) := by
    rw [eq_div_iff (mul_ne_zero hEx' hEy')]
    have q1 : c / ((a2 - a1) + x * (a1 - a0)) * ((a2 - a1) + x * (a1 - a0)) = c := div_mul_cancel₀ _ hEx'
    have q2 : c / ((a2 - a1) + y * (a1 - a0)) * ((a2 - a1) + y * (a1 - a0)) = c := div_mul_cancel₀ _ hEy'
    linear_combination (a2 * ((a2 - a1) + y * (a1 - a0))) * q1 - (a2 * ((a2 - a1) + x * (a1 - a0))) * q2
  have e2 : b2 * (c / ((b2 - b1) + x * (b1 - b0))) - b2 * (c / ((b2 - b1) + y * (b1 - b0))) =
      b2 * c * (b1 - b0) * (y - x) / (((b2 - b1) + x * (b1 - b0)) * ((b2 - b1) + y * (b1 - b0))) := by
    rw [eq_div_iff (mul_ne_zero hDx' hDy')]
    have q1 : c / ((b2 - b1) + x * (b1 - b0)) * ((b2 - b1) + x * (b1 - b0)) = c := div_mul_cancel₀ _ hDx'
    have q2 : c / ((b2 - b1) + y * (b1 - b0)) * ((b2 - b1) + y * (b1 - b0)) = c := div_mul_cancel₀ _ hDy'
    linear_combination (b2 * ((b2 - b1) + y * (b1 - b0))) * q1 - (b2 * ((b2 - b1) + x * (b1 - b0))) * q2
  have key : b2 * c * (b1 - b0) * (y - x) /
      (((b2 - b1) + x * (b1 - b0)) * ((b2 - b1) + y * (b1 - b0))) <
      a2 * c * (a1 - a0) * (y - x) / (((a2 - a1) + x * (a1 - a0)) * ((a2 - a1) + y * (a1 - a0))) := by
    rw [div_lt_div_iff₀ (mul_pos hDx hDy) (mul_pos hEx hEy)]
    have i1 : (b1 - b0) * ((a2 - a1) + x * (a1 - a0)) < (a1 - a0) * ((b2 - b1) + x * (b1 - b0)) := by
      nlinarith
    have i3 : b2 * ((a2 - a1) + y * (a1 - a0)) < a2 * ((b2 - b1) + y * (b1 - b0)) := by
      have hA : 0 < (1 - y) * (a2 * (b2 - b1) - b2 * (a2 - a1)) := mul_pos (by linarith) (by linarith)
      have hB : 0 ≤ y * (a0 * b2 - b0 * a2) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have h4 : (b1 - b0) * ((a2 - a1) + x * (a1 - a0)) * (b2 * ((a2 - a1) + y * (a1 - a0))) <
        (a1 - a0) * ((b2 - b1) + x * (b1 - b0)) * (a2 * ((b2 - b1) + y * (b1 - b0))) :=
      mul_lt_mul'' i1 i3 (mul_pos (by linarith) hEx).le (mul_pos (by linarith) hEy).le
    have hcyx : 0 < c * (y - x) := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left h4 hcyx]
  linarith

lemma P3_mono (a1 a2 b0 b1 b2 c x y : ℝ) (hc : 0 < c) (ha12 : a1 < a2) (ha2 : 0 < a2)
    (hb0 : 0 < b0) (hb01 : b0 < b1) (hb12 : b1 < b2) (hx : 0 ≤ x) (hxy : x < y) :
    a2 * (c * x / ((1 + x) * (a2 - a1))) - b2 * (c / ((b2 - b1) + x * (b1 - b0))) <
      a2 * (c * y / ((1 + y) * (a2 - a1))) - b2 * (c / ((b2 - b1) + y * (b1 - b0))) := by
  have hu : 0 < a2 - a1 := by linarith
  have hDx : 0 < (b2 - b1) + x * (b1 - b0) := by nlinarith
  have i1 : c * x / ((1 + x) * (a2 - a1)) < c * y / ((1 + y) * (a2 - a1)) := by
    rw [div_lt_div_iff₀ (by positivity) (by nlinarith)]
    have : 0 < c * (a2 - a1) * (y - x) := by have := mul_pos hc hu; nlinarith
    nlinarith
  have i2 : c / ((b2 - b1) + y * (b1 - b0)) < c / ((b2 - b1) + x * (b1 - b0)) :=
    div_lt_div_of_pos_left hc hDx (by nlinarith)
  have hb2 : 0 < b2 := by linarith
  nlinarith [mul_lt_mul_of_pos_left i1 ha2, mul_lt_mul_of_pos_left i2 hb2]

end WGSol

open WGSol in
theorem solution (c : ℝ) (fs fd : Tech) (hst : Standing c fs fd)
    (hratio : fs.f0 / fs.f2 > fd.f0 / fd.f2) (ws wd : ℝ → ℝ)
    (hws : ∀ δ ∈ Set.Icc (0 : ℝ) 1, IsLeast (FeasS c fs δ) (ws δ))
    (hwd : ∀ δ ∈ Set.Icc (0 : ℝ) 1, IsLeast (FeasD c fd δ) (wd δ)) :
    StrictAntiOn (fun δ => expWage fs (ws δ) - expWage fd (wd δ)) (Set.Icc 0 (deltaC fs)) ∧
      StrictMonoOn (fun δ => expWage fs (ws δ) - expWage fd (wd δ)) (Set.Ioc (deltaC fs) 1) ∧
      (∀ δ ∈ Set.Icc (0 : ℝ) 1, ∀ S : ℝ, 0 < S →
        (S < Sstar fs fd (expWage fs (ws δ) - expWage fd (wd δ)) →
            Vd fd S (wd δ) > Vs fs S (ws δ)) ∧
          (Sstar fs fd (expWage fs (ws δ) - expWage fd (wd δ)) ≤ S →
            Vs fs S (ws δ) ≥ Vd fd S (wd δ))) ∧
      (∀ δ ∈ Set.Ioo (deltaC fs) 1,
        0 < deriv (fun t => Sstar fs fd (expWage fs (ws t) - expWage fd (wd t))) δ) := by
  obtain ⟨hc, ⟨ha0, ha01, ha12, ha2⟩, ⟨hb0, hb01, hb12, hb2⟩, ⟨hA1s, hA1d⟩, hA2, hA3, hab⟩ := hst
  have hu : 0 < fs.f2 - fs.f1 := by linarith
  have hv : 0 < fs.f1 - fs.f0 := by linarith
  have hu' : 0 < fd.f2 - fd.f1 := by linarith
  have hv' : 0 < fd.f1 - fd.f0 := by linarith
  have ha2p : 0 < fs.f2 := by linarith
  have hb2p : 0 < fd.f2 := by linarith
  have hA1s' : fs.f2 - fs.f1 < fs.f1 - fs.f0 := by
    have := (lt_div_iff₀ hu).mp hA1s; linarith
  have hA1d' : fd.f1 - fd.f0 < fd.f2 - fd.f1 := by
    have := (div_lt_iff₀ hu').mp hA1d; linarith
  have hA2' : fs.f1 - fs.f0 < 2 * (fs.f2 - fs.f1) := by
    have := (div_lt_iff₀ hu).mp hA2; linarith
  have hA3' : fd.f1 * fs.f2 < fs.f1 * fd.f2 := (div_lt_div_iff₀ hb2p ha2p).mp hA3
  have hA3'' : fd.f2 * (fs.f2 - fs.f1) < fs.f2 * (fd.f2 - fd.f1) := by nlinarith
  have hr' : fd.f0 * fs.f2 < fs.f0 * fd.f2 := (div_lt_div_iff₀ hb2p ha2p).mp hratio
  -- thresholds
  have hm_half : deltaM fs < 1 / 2 := by
    unfold deltaM; rw [div_lt_iff₀ hv]; linarith
  have hC_half : 1 / 2 < deltaC fs := by
    unfold deltaC; rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ hv]; nlinarith
  have hC1 : deltaC fs < 1 := by
    unfold deltaC; rw [Real.sqrt_lt' one_pos, div_lt_iff₀ hv]; linarith
  have hmC : deltaM fs < deltaC fs := by linarith
  have hmv : deltaM fs * (fs.f1 - fs.f0) = 2 * fs.f1 - fs.f2 - fs.f0 := by
    unfold deltaM; exact div_mul_cancel₀ _ hv.ne'
  -- wage formulas
  have Hd : ∀ δ ∈ Set.Icc (0 : ℝ) 1, wd δ = c / ((fd.f2 - fd.f1) + δ * (fd.f1 - fd.f0)) :=
    fun δ hδ => wd_formula c fd hc hb0 hb01 hb12 δ hδ _ (hwd δ hδ)
  have H1 : ∀ δ ∈ Set.Icc (0 : ℝ) 1, δ < deltaM fs → ws δ = c * (1 - δ) / (fs.f2 - fs.f1) :=
    fun δ hδ h => ws_formula1 c fs hc ha0 ha01 ha12 hA2' δ hδ h _ (hws δ hδ)
  have H2 : ∀ δ ∈ Set.Icc (0 : ℝ) 1, deltaM fs ≤ δ → δ ≤ deltaC fs →
      ws δ = c / ((fs.f2 - fs.f1) + δ * (fs.f1 - fs.f0)) :=
    fun δ hδ h h' => ws_formula2 c fs hc ha0 ha01 ha12 δ hδ h h' _ (hws δ hδ)
  have H3 : ∀ δ ∈ Set.Icc (0 : ℝ) 1, deltaC fs < δ →
      ws δ = c * δ / ((1 + δ) * (fs.f2 - fs.f1)) :=
    fun δ hδ h => ws_formula3 c fs hc ha0 ha01 ha12 δ hδ (by linarith) h _ (hws δ hδ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hx1 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
    have hy1 : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1, by linarith [hy.2]⟩
    simp only [expWage]
    rw [Hd x hx1, Hd y hy1]
    rcases lt_or_ge y (deltaM fs) with hy' | hy'
    · rw [H1 x hx1 (by linarith), H1 y hy1 hy']
      exact P1_anti _ _ _ _ _ _ _ _ hc ha12 ha2p hb0 hb01 hb12 hA1d' hA3'' hx.1 hxy
    · rcases lt_or_ge x (deltaM fs) with hx' | hx'
      · rw [H1 x hx1 hx', H2 y hy1 hy' hy.2]
        set m := deltaM fs with hm
        have hm0 : 0 ≤ m := by linarith [hx.1]
        have hp1 := P1_anti _ _ _ _ _ _ _ _ hc ha12 ha2p hb0 hb01 hb12 hA1d' hA3'' hx.1 hx'
        have hEm : 0 < (fs.f2 - fs.f1) + m * (fs.f1 - fs.f0) := by nlinarith
        have hid : c * (1 - m) / (fs.f2 - fs.f1) = c / ((fs.f2 - fs.f1) + m * (fs.f1 - fs.f0)) := by
          rw [div_eq_div_iff hu.ne' hEm.ne']
          linear_combination (-c * m) * hmv
        rw [hid] at hp1
        rcases eq_or_lt_of_le hy' with he | hlt
        · rw [← he]; exact hp1
        · have hp2 := P2_anti _ _ _ _ _ _ _ _ _ hc ha0 ha01 ha12 hb0 hb01 hb12 hA1s' hA1d' hA3''
            hr' hm0 hlt (by linarith [hy.2])
          linarith
      · rw [H2 x hx1 hx' (by linarith [hy.2]), H2 y hy1 hy' hy.2]
        exact P2_anti _ _ _ _ _ _ _ _ _ hc ha0 ha01 ha12 hb0 hb01 hb12 hA1s' hA1d' hA3''
            hr' hx.1 hxy (by linarith [hy.2])
  · intro x hx y hy hxy
    have hC0 : 0 ≤ deltaC fs := Real.sqrt_nonneg _
    have hx1 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    have hy1 : y ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
    simp only [expWage]
    rw [Hd x hx1, Hd y hy1, H3 x hx1 hx.1, H3 y hy1 hy.1]
    exact P3_mono _ _ _ _ _ _ _ _ hc ha12 ha2p hb0 hb01 hb12 hx1.1 hxy
  · intro δ _ S _
    have hΔ : 0 < fs.f2 - fd.f2 := by linarith
    simp only [Sstar, Delta, Vd, Vs, expWage]
    have hk : ∀ g : ℝ, 2 / (fs.f2 - fd.f2) * g * (fs.f2 - fd.f2) = 2 * g := by
      intro g; field_simp
    constructor
    · intro h
      have := mul_lt_mul_of_pos_right h hΔ
      rw [hk] at this
      nlinarith
    · intro h
      have := mul_le_mul_of_nonneg_right h hΔ.le
      rw [hk] at this
      nlinarith
  · intro δ hδ
    have hC0 : 0 ≤ deltaC fs := Real.sqrt_nonneg _
    have hδ0 : 0 < δ := by linarith [hδ.1]
    have hΔ : 0 < fs.f2 - fd.f2 := by linarith
    have hD : 0 < (fd.f2 - fd.f1) + δ * (fd.f1 - fd.f0) := by nlinarith
    have hE : (1 + δ) * (fs.f2 - fs.f1) ≠ 0 := by positivity
    have heq : (fun t => Sstar fs fd (expWage fs (ws t) - expWage fd (wd t))) =ᶠ[nhds δ]
        (fun t => 2 / (fs.f2 - fd.f2) * (fs.f2 * (c * t / ((1 + t) * (fs.f2 - fs.f1))) -
          fd.f2 * (c / ((fd.f2 - fd.f1) + t * (fd.f1 - fd.f0))))) := by
      filter_upwards [Ioo_mem_nhds hδ.1 hδ.2] with t ht
      have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], ht.2.le⟩
      simp only [Sstar, Delta, expWage]
      rw [H3 t ht1 ht.1, Hd t ht1]
    rw [heq.deriv_eq]
    have h1 : HasDerivAt (fun t : ℝ => c * t) (c * 1) δ := (hasDerivAt_id δ).const_mul c
    have h2 : HasDerivAt (fun t : ℝ => (1 + t) * (fs.f2 - fs.f1)) (1 * (fs.f2 - fs.f1)) δ :=
      ((hasDerivAt_id δ).const_add 1).mul_const _
    have h3 : HasDerivAt (fun t : ℝ => (fd.f2 - fd.f1) + t * (fd.f1 - fd.f0))
        (1 * (fd.f1 - fd.f0)) δ := ((hasDerivAt_id δ).mul_const _).const_add _
    have h4 := (((h1.div h2 hE).const_mul fs.f2).sub
      (((hasDerivAt_const δ c).div h3 hD.ne').const_mul fd.f2)).const_mul (2 / (fs.f2 - fd.f2))
    have h5 : HasDerivAt (fun t => 2 / (fs.f2 - fd.f2) * (fs.f2 * (c * t / ((1 + t) * (fs.f2 - fs.f1))) -
          fd.f2 * (c / ((fd.f2 - fd.f1) + t * (fd.f1 - fd.f0))))) _ δ := h4
    rw [h5.deriv]
    apply mul_pos (div_pos two_pos hΔ)
    have X : 0 < (c * 1 * ((1 + δ) * (fs.f2 - fs.f1)) - c * δ * (1 * (fs.f2 - fs.f1))) /
        ((1 + δ) * (fs.f2 - fs.f1)) ^ 2 := by
      apply div_pos _ (by positivity)
      nlinarith [mul_pos hc hu]
    have Y : (0 * ((fd.f2 - fd.f1) + δ * (fd.f1 - fd.f0)) - c * (1 * (fd.f1 - fd.f0))) /
        ((fd.f2 - fd.f1) + δ * (fd.f1 - fd.f0)) ^ 2 < 0 := by
      apply div_neg_of_neg_of_pos _ (by positivity)
      nlinarith [mul_pos hc hv']
    linarith [mul_pos ha2p X, mul_neg_of_pos_of_neg hb2p Y]
