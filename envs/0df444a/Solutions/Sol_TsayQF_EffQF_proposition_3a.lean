-- Prove2me | solution 1 for TsayQF.EffQF.proposition_3a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:02:14.86481+00:00
-- url     : https://prove2.me/submissions/4f0c13ec-7a03-4447-a9e7-08045e58b5fb

import Mathlib
import Definitions.Def_TsayQF_EffQF_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace Aux_TQF3a
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

/-- Increment bound for the expected clipped purchase. -/
lemma clip_bound (hid : Integrable id ν) {lo Q Q' : ℝ} (hlo : lo ≤ Q) (hQ : Q ≤ Q') :
    ∫ μ, clip μ lo Q' ∂ν - ∫ μ, clip μ lo Q ∂ν ≤ (Q' - Q) * (1 - cdf ν Q) := by
  have hi : Integrable (fun μ : ℝ => clip μ lo Q' - clip μ lo Q) ν :=
    (int_clip hid lo Q').sub (int_clip hid lo Q)
  rw [← integral_sub (int_clip hid lo Q') (int_clip hid lo Q)]
  have hpt : ∀ μ : ℝ, clip μ lo Q' - clip μ lo Q ≤
      (Set.Ioi Q).indicator (fun _ => Q' - Q) μ := by
    intro μ
    simp only [Set.indicator, Set.mem_Ioi, clip]
    split_ifs <;> simp only [max_def, min_def] <;> split_ifs <;> linarith
  calc _ ≤ ∫ μ, (Set.Ioi Q).indicator (fun _ => Q' - Q) μ ∂ν :=
        integral_mono hi ((integrable_const _).indicator measurableSet_Ioi) hpt
    _ = (Q' - Q) * (1 - cdf ν Q) := by
        rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, real_Ioi]; ring

/-- Decomposition of the retailer's profit with clipped purchase. -/
lemma retail_decomp (hid : Integrable id ν) (D : Data) (c lo Q0 : ℝ) (h : lo ≤ Q0) :
    ∫ μ, G D c (clip μ lo Q0) μ ∂ν =
      (D.p - c) * ∫ μ, μ ∂ν - (c - D.u) * ∫ μ, max (lo - μ) 0 ∂ν
        - (D.p + D.s - c) * ∫ μ, max (μ - Q0) 0 ∂ν := by
  have hpt : ∀ μ : ℝ, G D c (clip μ lo Q0) μ =
      (D.p - c) * μ - (c - D.u) * max (lo - μ) 0 - (D.p + D.s - c) * max (μ - Q0) 0 := by
    intro μ
    simp only [G, clip]
    rcases le_total μ lo with h1 | h1
    · have e1 : min μ Q0 = μ := min_eq_left (h1.trans h)
      have e2 : max lo μ = lo := max_eq_left h1
      rw [e1, e2, min_eq_left h1, max_eq_right (by linarith : μ - lo ≤ 0),
        max_eq_left (by linarith : (0:ℝ) ≤ lo - μ), max_eq_right (by linarith : μ - Q0 ≤ 0)]
      ring
    · rcases le_total μ Q0 with h2 | h2
      · rw [min_eq_left h2, max_eq_right h1, min_self, sub_self, max_self,
          max_eq_right (by linarith : lo - μ ≤ 0), max_eq_right (by linarith : μ - Q0 ≤ 0)]
        ring
      · rw [min_eq_right h2, max_eq_right h, min_eq_right h2,
          max_eq_left (by linarith : (0:ℝ) ≤ μ - Q0), max_eq_right (by linarith : Q0 - μ ≤ 0),
          max_eq_right (by linarith : lo - μ ≤ 0)]
        ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have i1 : Integrable (fun μ : ℝ => (D.p - c) * μ) ν := hid.const_mul _
  have i2 : Integrable (fun μ : ℝ => (c - D.u) * max (lo - μ) 0) ν :=
    (int_posB hid lo).const_mul _
  have i3 : Integrable (fun μ : ℝ => (D.p + D.s - c) * max (μ - Q0) 0) ν :=
    (int_posA hid Q0).const_mul _
  have i12 : Integrable (fun μ : ℝ => (D.p - c) * μ - (c - D.u) * max (lo - μ) 0) ν :=
    i1.sub i2
  rw [integral_sub i12 i3, integral_sub i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul]

lemma no_atom (hc : Continuous (cdf ν)) (x : ℝ) : ν.real {x} = 0 := by
  have h1 : ν {x} = 0 := by
    rw [← measure_cdf (μ := ν), StieltjesFunction.measure_singleton,
      (hc.continuousWithinAt).leftLim_eq, sub_self, ENNReal.ofReal_zero]
  simp [Measure.real, h1]

lemma int_Ici (hc : Continuous (cdf ν)) (D : Data) (c r : ℝ) :
    ∫ μ in Set.Ici r, Gderiv D c r μ ∂ν = (D.p + D.s - c) * (1 - cdf ν r) := by
  rw [← integral_indicator measurableSet_Ici]
  have hpt : ∀ μ : ℝ, (Set.Ici r).indicator (fun μ => Gderiv D c r μ) μ =
      (Set.Ioi r).indicator (fun _ => D.p + D.s - c) μ +
        ({r} : Set ℝ).indicator (fun _ => D.u - c) μ := by
    intro μ
    simp only [Set.indicator, Set.mem_Ici, Set.mem_Ioi, Set.mem_singleton_iff, Gderiv]
    rcases lt_trichotomy μ r with h | h | h
    · rw [if_neg (not_le.2 h), if_neg (not_lt.2 h.le), if_neg h.ne]; ring
    · subst h; simp
    · rw [if_pos h.le, if_pos h, if_pos h, if_neg h.ne']; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_add ((integrable_const _).indicator measurableSet_Ioi)
      ((integrable_const _).indicator (measurableSet_singleton r)),
    integral_indicator_const _ measurableSet_Ioi,
    integral_indicator_const _ (measurableSet_singleton r), no_atom hc, real_Ioi]
  simp only [smul_eq_mul, zero_mul, add_zero]; ring

lemma int_Iic (D : Data) (c r : ℝ) :
    ∫ μ in Set.Iic r, Gderiv D c r μ ∂ν = (D.u - c) * cdf ν r := by
  have : ∫ μ in Set.Iic r, Gderiv D c r μ ∂ν = ∫ μ in Set.Iic r, (D.u - c) ∂ν := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro μ hμ
    simp only [Gderiv]
    rw [if_neg (not_lt.2 hμ)]
  rw [this, setIntegral_const, smul_eq_mul, ← cdf_eq_real]; ring

end Aux_TQF3a

open TsayQF.EffQF Aux_TQF3a in
theorem solution (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hΘ : StrictMono (cdf ν)) (hΘd : Differentiable ℝ (cdf ν)) (hν : MemLp id 2 ν)
    (c : ℝ) (hcu : D.u < c) (hcp : c < D.p + D.s)
    (α ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω < 1) (hα : -ω ≤ α)
    (h0 : (1 - ω) * (c - D.u) * cdf ν 0 < (1 + α) * (D.p + D.s - c) * (1 - cdf ν 0)) :
    let eq3 : ℝ → Prop := fun q =>
      (1 + α) * ∫ μ in Set.Ici (q * (1 + α)), Gderiv D c (q * (1 + α)) μ ∂ν =
        -((1 - ω) * ∫ μ in Set.Iic (q * (1 - ω)), Gderiv D c (q * (1 - ω)) μ ∂ν)
    (∃! q, 0 < q ∧ eq3 q) ∧
      ∀ q, 0 ≤ q → (IsMaxOn (forecastProfit D ν c α ω) (Set.Ici 0) q ↔ (0 < q ∧ eq3 q)) := by
  intro eq3
  have hid : Integrable id ν := hν.integrable (by norm_num)
  have hc : Continuous (cdf ν) := hΘd.continuous
  set F := cdf ν with hF
  set k := 1 - ω with hk
  set l := 1 + α with hl
  have hk0 : 0 < k := by rw [hk]; linarith
  have hkl : k ≤ l := by rw [hk, hl]; linarith
  have hl0 : 0 < l := lt_of_lt_of_le hk0 hkl
  set A := c - D.u with hA
  set B := D.p + D.s - c with hB
  have hA0 : 0 < A := by rw [hA]; linarith
  have hB0 : 0 < B := by rw [hB]; linarith
  let Dm : ℝ → ℝ := fun x => A * k * F (x * k) - B * l * (1 - F (x * l))
  have hDmono : StrictMono Dm := by
    intro x y hxy
    have h1 : F (x * k) < F (y * k) := hΘ (mul_lt_mul_of_pos_right hxy hk0)
    have h2 : F (x * l) < F (y * l) := hΘ (mul_lt_mul_of_pos_right hxy hl0)
    show A * k * F (x * k) - B * l * (1 - F (x * l)) < A * k * F (y * k) - B * l * (1 - F (y * l))
    have e1 : A * k * F (x * k) < A * k * F (y * k) := mul_lt_mul_of_pos_left h1 (mul_pos hA0 hk0)
    have e2 : B * l * (1 - F (y * l)) < B * l * (1 - F (x * l)) :=
      mul_lt_mul_of_pos_left (by linarith) (mul_pos hB0 hl0)
    linarith
  have heq3 : ∀ q, eq3 q ↔ Dm q = 0 := by
    intro q
    show (l * ∫ μ in Set.Ici (q * l), Gderiv D c (q * l) μ ∂ν =
        -(k * ∫ μ in Set.Iic (q * k), Gderiv D c (q * k) μ ∂ν)) ↔
      A * k * F (q * k) - B * l * (1 - F (q * l)) = 0
    rw [int_Ici hc, int_Iic, ← hB, ← hF]
    have e : D.u - c = -A := by rw [hA]; ring
    rw [e]
    constructor <;> intro h <;> linarith only [h]
  have hD0 : Dm 0 < 0 := by
    show A * k * F (0 * k) - B * l * (1 - F (0 * l)) < 0
    simp only [zero_mul]
    have : k * A * F 0 < l * B * (1 - F 0) := h0
    linarith only [this]
  -- a point where Dm is positive
  have hθ : B * l / (A * k + B * l) < 1 := by
    rw [div_lt_one (by positivity)]; linarith [mul_pos hA0 hk0]
  obtain ⟨t, ht⟩ := ((tendsto_cdf_atTop (μ := ν)).eventually_const_lt hθ).exists
  set t1 := max t 1 with ht1
  have ht1F : B * l / (A * k + B * l) < F t1 :=
    lt_of_lt_of_le ht (hΘ.monotone (le_max_left _ _))
  have ht10 : 0 < t1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set x1 := t1 / k with hx1
  have hx1k : x1 * k = t1 := by rw [hx1]; field_simp
  have hx10 : 0 < x1 := div_pos ht10 hk0
  have hD1 : 0 < Dm x1 := by
    show 0 < A * k * F (x1 * k) - B * l * (1 - F (x1 * l))
    have hmono : F (x1 * k) ≤ F (x1 * l) :=
      hΘ.monotone (mul_le_mul_of_nonneg_left hkl hx10.le)
    rw [hx1k] at hmono ⊢
    have hpos : 0 < A * k + B * l := by positivity
    have := (div_lt_iff₀ hpos).1 ht1F
    nlinarith [mul_pos hB0 hl0]
  have hDc : Continuous Dm := by
    show Continuous fun x => A * k * F (x * k) - B * l * (1 - F (x * l))
    fun_prop
  obtain ⟨qs, hqsI, hqs⟩ := intermediate_value_Icc hx10.le hDc.continuousOn ⟨hD0.le, hD1.le⟩
  have hqs0 : 0 < qs := by
    rcases eq_or_lt_of_le hqsI.1 with h | h
    · rw [← h] at hqs; linarith
    · exact h
  -- forecast-profit bracket
  have fdecomp : ∀ q, 0 ≤ q → forecastProfit D ν c α ω q =
      (D.p - c) * ∫ μ, μ ∂ν - A * ∫ μ, max (q * k - μ) 0 ∂ν
        - B * ∫ μ, max (μ - q * l) 0 ∂ν := by
    intro q hq
    unfold forecastProfit retailerProfit
    rw [← hk, ← hl]
    have h := retail_decomp hid D c (q * k) (q * l) (mul_le_mul_of_nonneg_left hkl hq)
    rw [← hA, ← hB] at h
    exact h
  have finc : ∀ x y, 0 ≤ x → x ≤ y →
      -(y - x) * Dm y ≤ forecastProfit D ν c α ω y - forecastProfit D ν c α ω x ∧
      forecastProfit D ν c α ω y - forecastProfit D ν c α ω x ≤ -(y - x) * Dm x := by
    intro x y hx hxy
    rw [fdecomp y (hx.trans hxy), fdecomp x hx]
    obtain ⟨e1, e2⟩ := E1_bounds hid (mul_le_mul_of_nonneg_right hxy hk0.le)
    obtain ⟨e3, e4⟩ := E2_bounds hid (mul_le_mul_of_nonneg_right hxy hl0.le)
    have r1 : (y * k - x * k) = (y - x) * k := by ring
    have r2 : (y * l - x * l) = (y - x) * l := by ring
    rw [r1] at e1 e2; rw [r2] at e3 e4
    show -(y - x) * (A * k * F (y * k) - B * l * (1 - F (y * l))) ≤ _ ∧
      _ ≤ -(y - x) * (A * k * F (x * k) - B * l * (1 - F (x * l)))
    constructor
    · have := mul_le_mul_of_nonneg_left e2 hA0.le
      have := mul_le_mul_of_nonneg_left e3 hB0.le
      linarith
    · have := mul_le_mul_of_nonneg_left e1 hA0.le
      have := mul_le_mul_of_nonneg_left e4 hB0.le
      linarith
  have hiff : ∀ q, (0 < q ∧ eq3 q) ↔ q = qs := by
    intro q
    rw [heq3]
    constructor
    · rintro ⟨-, h⟩; exact hDmono.injective (h.trans hqs.symm)
    · rintro rfl; exact ⟨hqs0, hqs⟩
  refine ⟨⟨qs, (hiff qs).2 rfl, fun q hq => (hiff q).1 hq⟩, ?_⟩
  intro q hq
  rw [hiff]
  constructor
  · intro hmax
    have hmax' := isMaxOn_iff.1 hmax
    by_contra hne
    obtain ⟨m, hmd⟩ : ∃ m : ℝ, m = (q + qs) / 2 := ⟨_, rfl⟩
    have hm0 : (0:ℝ) ≤ m := by rw [hmd]; linarith only [hq, hqs0]
    have hle : forecastProfit D ν c α ω m ≤ forecastProfit D ν c α ω q := hmax' m hm0
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hqm : q < m := by rw [hmd]; linarith only [hlt]
      have hm : Dm m < 0 := by rw [← hqs]; exact hDmono (by rw [hmd]; linarith only [hlt])
      have h := (finc q m hq hqm.le).1
      have : 0 < -(m - q) * Dm m := mul_pos_of_neg_of_neg (by linarith only [hqm]) hm
      linarith only [h, hle, this]
    · have hqm : m < q := by rw [hmd]; linarith only [hgt]
      have hm : 0 < Dm m := by rw [← hqs]; exact hDmono (by rw [hmd]; linarith only [hgt])
      have h := (finc m q hm0 hqm.le).2
      have : -(q - m) * Dm m < 0 := mul_neg_of_neg_of_pos (by linarith only [hqm]) hm
      linarith only [h, hle, this]
  · rintro rfl
    refine isMaxOn_iff.2 fun z hz => ?_
    have hz : (0:ℝ) ≤ z := hz
    rcases le_total z q with h | h
    · have h' := (finc z q hz h).1
      rw [hqs, mul_zero] at h'; linarith only [h']
    · have h' := (finc q z hqs0.le h).2
      rw [hqs, mul_zero] at h'; linarith only [h']
