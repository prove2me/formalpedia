-- Prove2me | solution 1 for TsayQF.EffQF.cc_optimal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T14:58:19.209988+00:00
-- url     : https://prove2.me/submissions/6bcc531b-a235-4ca7-9ac0-68d573accec5

import Mathlib
import Definitions.Def_TsayQF_EffQF_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace Aux_TQFcc
open TsayQF.EffQF

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

lemma int_posA (hid : Integrable id ν) (a : ℝ) : Integrable (fun μ : ℝ => max (μ - a) 0) ν :=
  (hid.sub (integrable_const a)).pos_part

lemma int_posB (hid : Integrable id ν) (a : ℝ) : Integrable (fun μ : ℝ => max (a - μ) 0) ν :=
  ((integrable_const a).sub hid).pos_part

lemma int_min (hid : Integrable id ν) (a : ℝ) : Integrable (fun μ : ℝ => min μ a) ν := by
  have h : (fun μ : ℝ => min μ a) = fun μ => id μ - max (μ - a) 0 := by
    funext μ; simp only [id]
    rcases le_total μ a with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  rw [h]; exact hid.sub (int_posA hid a)

lemma int_clip (hid : Integrable id ν) (lo Q : ℝ) :
    Integrable (fun μ : ℝ => clip μ lo Q) ν := by
  have h : (fun μ : ℝ => clip μ lo Q) = fun μ => lo + max (min μ Q - lo) 0 := by
    funext μ; simp only [clip]
    rcases le_total (min μ Q) lo with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  rw [h]
  exact (integrable_const lo).add (((int_min hid Q).sub (integrable_const lo)).pos_part)

lemma real_Ioi (t : ℝ) : ν.real (Set.Ioi t) = 1 - cdf ν t := by
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real]

/-- Bounds on the increments of `t ↦ E (t - μ)⁺`. -/
lemma E1_bounds (hid : Integrable id ν) {a b : ℝ} (hab : a ≤ b) :
    (b - a) * cdf ν a ≤ ∫ μ, max (b - μ) 0 ∂ν - ∫ μ, max (a - μ) 0 ∂ν ∧
    ∫ μ, max (b - μ) 0 ∂ν - ∫ μ, max (a - μ) 0 ∂ν ≤ (b - a) * cdf ν b := by
  have hi : Integrable (fun μ : ℝ => max (b - μ) 0 - max (a - μ) 0) ν :=
    (int_posB hid b).sub (int_posB hid a)
  rw [← integral_sub (int_posB hid b) (int_posB hid a)]
  constructor
  · have hpt : ∀ μ : ℝ, (Set.Iic a).indicator (fun _ => b - a) μ ≤
        max (b - μ) 0 - max (a - μ) 0 := by
      intro μ
      simp only [Set.indicator, Set.mem_Iic]
      split_ifs <;> simp only [max_def] <;> split_ifs <;> linarith
    calc (b - a) * cdf ν a = ∫ μ, (Set.Iic a).indicator (fun _ => b - a) μ ∂ν := by
          rw [integral_indicator_const _ measurableSet_Iic, smul_eq_mul, ← cdf_eq_real]; ring
      _ ≤ _ := integral_mono ((integrable_const _).indicator measurableSet_Iic) hi hpt
  · have hpt : ∀ μ : ℝ, max (b - μ) 0 - max (a - μ) 0 ≤
        (Set.Iic b).indicator (fun _ => b - a) μ := by
      intro μ
      simp only [Set.indicator, Set.mem_Iic]
      split_ifs <;> simp only [max_def] <;> split_ifs <;> linarith
    calc _ ≤ ∫ μ, (Set.Iic b).indicator (fun _ => b - a) μ ∂ν :=
          integral_mono hi ((integrable_const _).indicator measurableSet_Iic) hpt
      _ = (b - a) * cdf ν b := by
          rw [integral_indicator_const _ measurableSet_Iic, smul_eq_mul, ← cdf_eq_real]; ring

/-- Bounds on the decrements of `t ↦ E (μ - t)⁺`. -/
lemma E2_bounds (hid : Integrable id ν) {a b : ℝ} (hab : a ≤ b) :
    (b - a) * (1 - cdf ν b) ≤ ∫ μ, max (μ - a) 0 ∂ν - ∫ μ, max (μ - b) 0 ∂ν ∧
    ∫ μ, max (μ - a) 0 ∂ν - ∫ μ, max (μ - b) 0 ∂ν ≤ (b - a) * (1 - cdf ν a) := by
  have hi : Integrable (fun μ : ℝ => max (μ - a) 0 - max (μ - b) 0) ν :=
    (int_posA hid a).sub (int_posA hid b)
  rw [← integral_sub (int_posA hid a) (int_posA hid b)]
  constructor
  · have hpt : ∀ μ : ℝ, (Set.Ioi b).indicator (fun _ => b - a) μ ≤
        max (μ - a) 0 - max (μ - b) 0 := by
      intro μ
      simp only [Set.indicator, Set.mem_Ioi]
      split_ifs <;> simp only [max_def] <;> split_ifs <;> linarith
    calc (b - a) * (1 - cdf ν b) = ∫ μ, (Set.Ioi b).indicator (fun _ => b - a) μ ∂ν := by
          rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, real_Ioi]; ring
      _ ≤ _ := integral_mono ((integrable_const _).indicator measurableSet_Ioi) hi hpt
  · have hpt : ∀ μ : ℝ, max (μ - a) 0 - max (μ - b) 0 ≤
        (Set.Ioi a).indicator (fun _ => b - a) μ := by
      intro μ
      simp only [Set.indicator, Set.mem_Ioi]
      split_ifs <;> simp only [max_def] <;> split_ifs <;> linarith
    calc _ ≤ ∫ μ, (Set.Ioi a).indicator (fun _ => b - a) μ ∂ν :=
          integral_mono hi ((integrable_const _).indicator measurableSet_Ioi) hpt
      _ = (b - a) * (1 - cdf ν a) := by
          rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, real_Ioi]; ring

lemma cc_decomp (hid : Integrable id ν) (D : Data) (Q : ℝ) :
    ccProfit D ν Q = (D.p - D.m) * ∫ μ, μ ∂ν - (D.m - D.u) * ∫ μ, max (Q - μ) 0 ∂ν
        - (D.p + D.s - D.m) * ∫ μ, max (μ - Q) 0 ∂ν := by
  unfold ccProfit
  have hpt : ∀ μ : ℝ, D.p * min μ Q - D.s * max (μ - Q) 0 + D.u * max (Q - μ) 0 =
      (D.p - D.m) * μ - (D.m - D.u) * max (Q - μ) 0 - (D.p + D.s - D.m) * max (μ - Q) 0
        + D.m * Q := by
    intro μ
    rcases le_total μ Q with h | h
    · rw [min_eq_left h, max_eq_right (by linarith : μ - Q ≤ 0),
        max_eq_left (by linarith : (0:ℝ) ≤ Q - μ)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ μ - Q),
        max_eq_right (by linarith : Q - μ ≤ 0)]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have i1 : Integrable (fun μ : ℝ => (D.p - D.m) * μ) ν := hid.const_mul _
  have i2 : Integrable (fun μ : ℝ => (D.m - D.u) * max (Q - μ) 0) ν :=
    (int_posB hid Q).const_mul _
  have i3 : Integrable (fun μ : ℝ => (D.p + D.s - D.m) * max (μ - Q) 0) ν :=
    (int_posA hid Q).const_mul _
  have i12 : Integrable (fun μ : ℝ => (D.p - D.m) * μ - (D.m - D.u) * max (Q - μ) 0) ν :=
    i1.sub i2
  have i123 : Integrable (fun μ : ℝ => (D.p - D.m) * μ - (D.m - D.u) * max (Q - μ) 0
      - (D.p + D.s - D.m) * max (μ - Q) 0) ν := i12.sub i3
  rw [integral_add i123 (integrable_const _), integral_sub i12 i3, integral_sub i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

end Aux_TQFcc

open TsayQF.EffQF Aux_TQFcc in
theorem solution (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hΘ : StrictMono (cdf ν)) (hΘd : Differentiable ℝ (cdf ν)) (hν : MemLp id 2 ν) :
    (∃ Q, cdf ν Q = kS D) ∧
      ∀ Q, IsMaxOn (ccProfit D ν) Set.univ Q ↔ cdf ν Q = kS D := by
  have hid : Integrable id ν := hν.integrable (by norm_num)
  set A := D.m - D.u with hA
  set B := D.p + D.s - D.m with hB
  set P := D.p + D.s - D.u with hP
  have hA0 : 0 < A := by rw [hA]; linarith [D.hum]
  have hB0 : 0 < B := by rw [hB]; linarith [D.hmp, D.hs]
  have hPAB : P = A + B := by rw [hP, hA, hB]; ring
  have hP0 : 0 < P := by rw [hPAB]; linarith
  have hkS : kS D = B / P := by unfold kS; rw [hB, hP]
  have hkS0 : 0 < kS D := by rw [hkS]; positivity
  have hkS1 : kS D < 1 := by rw [hkS, div_lt_one hP0]; linarith
  -- existence
  have hex : ∃ Q, cdf ν Q = kS D := by
    obtain ⟨x0, hx0⟩ := ((tendsto_cdf_atBot (μ := ν)).eventually_lt_const hkS0).exists
    obtain ⟨x1, hx1⟩ := ((tendsto_cdf_atTop (μ := ν)).eventually_const_lt hkS1).exists
    have h01 : x0 ≤ x1 := by
      by_contra h; have h := not_le.1 h
      have := hΘ h; linarith
    have hsub := intermediate_value_Icc h01 (hΘd.continuous.continuousOn)
    obtain ⟨Q, -, hQ⟩ := hsub ⟨hx0.le, hx1.le⟩
    exact ⟨Q, hQ⟩
  refine ⟨hex, ?_⟩
  obtain ⟨Qs, hQs⟩ := hex
  -- marginal
  let Dm : ℝ → ℝ := fun x => A * cdf ν x - B * (1 - cdf ν x)
  have hDmono : StrictMono Dm := by
    intro x y hxy
    have h1 := hΘ hxy
    show A * cdf ν x - B * (1 - cdf ν x) < A * cdf ν y - B * (1 - cdf ν y)
    have e1 : A * cdf ν x < A * cdf ν y := mul_lt_mul_of_pos_left h1 hA0
    have e2 : B * (1 - cdf ν y) < B * (1 - cdf ν x) :=
      mul_lt_mul_of_pos_left (by linarith only [h1]) hB0
    linarith only [e1, e2]
  have hDzero : ∀ x, Dm x = 0 ↔ cdf ν x = kS D := by
    intro x
    show A * cdf ν x - B * (1 - cdf ν x) = 0 ↔ _
    rw [hkS, eq_div_iff hP0.ne', hPAB]
    constructor <;> intro h <;> linarith only [h]
  have hDs : Dm Qs = 0 := (hDzero Qs).2 hQs
  have finc : ∀ x y, x ≤ y →
      -(y - x) * Dm y ≤ ccProfit D ν y - ccProfit D ν x ∧
      ccProfit D ν y - ccProfit D ν x ≤ -(y - x) * Dm x := by
    intro x y hxy
    rw [cc_decomp hid D y, cc_decomp hid D x, ← hA, ← hB]
    obtain ⟨e1, e2⟩ := E1_bounds hid (ν := ν) hxy
    obtain ⟨e3, e4⟩ := E2_bounds hid (ν := ν) hxy
    show -(y - x) * (A * cdf ν y - B * (1 - cdf ν y)) ≤ _ ∧
      _ ≤ -(y - x) * (A * cdf ν x - B * (1 - cdf ν x))
    constructor
    · have := mul_le_mul_of_nonneg_left e2 hA0.le
      have := mul_le_mul_of_nonneg_left e3 hB0.le
      linarith
    · have := mul_le_mul_of_nonneg_left e1 hA0.le
      have := mul_le_mul_of_nonneg_left e4 hB0.le
      linarith
  have hmaxs : ∀ z, ccProfit D ν z ≤ ccProfit D ν Qs := by
    intro z
    rcases le_total z Qs with h | h
    · have h' := (finc z Qs h).1
      rw [hDs, mul_zero] at h'; linarith only [h']
    · have h' := (finc Qs z h).2
      rw [hDs, mul_zero] at h'; linarith only [h']
  intro Q
  constructor
  · intro hmax
    have hmax' := isMaxOn_iff.1 hmax
    suffices hQ : Q = Qs by rw [hQ]; exact hQs
    by_contra hne
    obtain ⟨m, hmd⟩ : ∃ m : ℝ, m = (Q + Qs) / 2 := ⟨_, rfl⟩
    have hle : ccProfit D ν m ≤ ccProfit D ν Q := hmax' m (Set.mem_univ _)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hqm : Q < m := by rw [hmd]; linarith only [hlt]
      have hm : Dm m < 0 := by rw [← hDs]; exact hDmono (by rw [hmd]; linarith only [hlt])
      have h := (finc Q m hqm.le).1
      have : 0 < -(m - Q) * Dm m := mul_pos_of_neg_of_neg (by linarith only [hqm]) hm
      linarith only [h, hle, this]
    · have hqm : m < Q := by rw [hmd]; linarith only [hgt]
      have hm : 0 < Dm m := by rw [← hDs]; exact hDmono (by rw [hmd]; linarith only [hgt])
      have h := (finc m Q hqm.le).2
      have : -(Q - m) * Dm m < 0 := mul_neg_of_neg_of_pos (by linarith only [hqm]) hm
      linarith only [h, hle, this]
  · intro hQ
    have hQQ : Q = Qs := hΘ.injective (hQ.trans hQs.symm)
    rw [hQQ]
    exact isMaxOn_iff.2 fun z _ => hmaxs z
