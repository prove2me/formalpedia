-- Prove2me | solution 1 for TsayQF.EffQF.proposition_6a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T14:53:21.869676+00:00
-- url     : https://prove2.me/submissions/a841fcc3-e7b7-4153-9b71-aeb48709e19d

import Mathlib
import Definitions.Def_TsayQF_EffQF_Model
import Theorems.Thm_TsayQF_EffQF_system_profit_eq_cc

open MeasureTheory ProbabilityTheory

namespace Aux_TQF6a
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

end Aux_TQF6a

open TsayQF.EffQF Aux_TQF6a in
theorem solution (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hΘ : StrictMono (cdf ν)) (hΘd : Differentiable ℝ (cdf ν)) (hν : MemLp id 2 ν)
    (α ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω < 1) (hα : -ω ≤ α)
    (Qcc : ℝ) (hQcc : cdf ν Qcc = kS D) (hpos : 0 < Qcc) :
    let c := cbar D ν (psi α ω) Qcc
    let qhat := Qcc / (1 + α)
    (∀ q, 0 ≤ q → (IsMaxOn (forecastProfit D ν c α ω) (Set.Ici 0) q ↔ q = qhat)) ∧
    (∀ Q, qhat * (1 + α) ≤ Q →
      (IsMaxOn (emProfit D ν c ω qhat) (Set.Ici (qhat * (1 + α))) Q ↔ Q = qhat * (1 + α))) ∧
    (∀ Q, ccProfit D ν Q ≤
      forecastProfit D ν c α ω qhat + emProfit D ν c ω qhat (qhat * (1 + α))) := by
  intro c qhat
  have hcdef : c = cbar D ν (psi α ω) Qcc := rfl
  have hqdef : qhat = Qcc / (1 + α) := rfl
  clear_value c qhat
  have hid : Integrable id ν := hν.integrable (by norm_num)
  set F := cdf ν with hF
  set k := 1 - ω with hk
  set l := 1 + α with hl
  have hk0 : 0 < k := by rw [hk]; linarith
  have hkl : k ≤ l := by rw [hk, hl]; linarith
  have hl0 : 0 < l := lt_of_lt_of_le hk0 hkl
  have hqhat0 : 0 < qhat := by rw [hqdef]; exact div_pos hpos hl0
  have hqhatl : qhat * l = Qcc := by
    rw [hqdef]; field_simp
  set a := qhat * k with ha
  have ha' : (1 / psi α ω) * Qcc = a := by
    rw [ha, ← hqhatl]; unfold psi; rw [← hk, ← hl]; field_simp
  have hFpos : ∀ x, 0 < F x := fun x =>
    lt_of_le_of_lt (cdf_nonneg ν (x - 1)) (hΘ (by linarith : x - 1 < x))
  set P := D.p + D.s - D.u with hP
  have hP0 : 0 < P := by rw [hP]; linarith [D.hmp, D.hum, D.hs]
  have hmu : 0 < D.m - D.u := by linarith [D.hum]
  have h1k : P * (1 - kS D) = D.m - D.u := by
    unfold kS; rw [← hP]; field_simp; rw [hP]; ring
  set d := (1 / psi α ω) * F a + (D.m - D.u) / P with hd
  have hpsi : 1 / psi α ω = k / l := by unfold psi; rw [← hk, ← hl]; field_simp
  have hd0 : 0 < d := by
    rw [hd, hpsi]; have := hFpos a; positivity
  have hdl : d * l = k * F a + l * (1 - kS D) := by
    rw [hd, hpsi, ← h1k]; field_simp
  set A := c - D.u with hA
  have hcA : c = D.u + (D.m - D.u) / d := by
    rw [hcdef]; unfold cbar; rw [ha', ← hF, ← hP]
  have hAd : A * d = D.m - D.u := by rw [hA, hcA]; field_simp; ring
  have hA0 : 0 < A := by rw [hA, hcA]; simp only [add_sub_cancel_left]; positivity
  have hAP : A < P := by
    have : P * d > D.m - D.u := by
      rw [hd, hpsi, mul_add]
      have : P * ((D.m - D.u) / P) = D.m - D.u := by field_simp
      rw [this]; have := hFpos a; have : 0 < P * (k / l * F a) := by positivity
      linarith
    nlinarith
  set B := D.p + D.s - c with hB
  have hBA : B = P - A := by rw [hB, hP, hA]; ring
  have hB0 : 0 < B := by rw [hBA]; linarith
  -- marginal function of the forecast problem
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
  have hDq : Dm qhat = 0 := by
    show A * k * F (qhat * k) - B * l * (1 - F (qhat * l)) = 0
    rw [← ha, hqhatl, hF, hQcc, hBA]
    linear_combination (-A) * hdl + l * hAd - l * h1k
  -- increment bounds for the forecast profit
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
    have hyx : 0 ≤ y - x := by linarith
    show -(y - x) * (A * k * F (y * k) - B * l * (1 - F (y * l))) ≤ _ ∧
      _ ≤ -(y - x) * (A * k * F (x * k) - B * l * (1 - F (x * l)))
    constructor
    · have := mul_le_mul_of_nonneg_left e2 hA0.le
      have := mul_le_mul_of_nonneg_left e3 hB0.le
      linarith
    · have := mul_le_mul_of_nonneg_left e1 hA0.le
      have := mul_le_mul_of_nonneg_left e4 hB0.le
      linarith
  refine ⟨?_, ?_, ?_⟩
  · -- clause 1
    intro q hq
    constructor
    · intro hmax
      have hmax' := isMaxOn_iff.1 hmax
      by_contra hne
      obtain ⟨m, hmd⟩ : ∃ m : ℝ, m = (q + qhat) / 2 := ⟨_, rfl⟩
      have hm0 : (0:ℝ) ≤ m := by rw [hmd]; linarith only [hq, hqhat0]
      have hle : forecastProfit D ν c α ω m ≤ forecastProfit D ν c α ω q := hmax' m hm0
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hqm : q < m := by rw [hmd]; linarith only [hlt]
        have hm : Dm m < 0 := by rw [← hDq]; exact hDmono (by rw [hmd]; linarith only [hlt])
        have h := (finc q m hq hqm.le).1
        have : 0 < -(m - q) * Dm m := mul_pos_of_neg_of_neg (by linarith only [hqm]) hm
        linarith only [h, hle, this]
      · have hqm : m < q := by rw [hmd]; linarith only [hgt]
        have hm : 0 < Dm m := by rw [← hDq]; exact hDmono (by rw [hmd]; linarith only [hgt])
        have h := (finc m q hm0 hqm.le).2
        have : -(q - m) * Dm m < 0 := mul_neg_of_neg_of_pos (by linarith only [hqm]) hm
        linarith only [h, hle, this]
    · rintro rfl
      refine isMaxOn_iff.2 fun z hz => ?_
      have hz : (0:ℝ) ≤ z := hz
      rcases le_total z q with h | h
      · have h' := (finc z q hz h).1
        rw [hDq, mul_zero] at h'; linarith only [h']
      · have h' := (finc q z hqhat0.le h).2
        rw [hDq, mul_zero] at h'; linarith only [h']
  · -- clause 2
    have hlo : qhat * (1 - ω) ≤ qhat * (1 + α) := mul_le_mul_of_nonneg_left hkl hqhat0.le
    have hkS1 : 0 < 1 - kS D := by
      by_contra hc; have hc := not_lt.1 hc
      have : P * (1 - kS D) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hP0.le hc
      linarith only [this, h1k, hmu]
    have hAk : A * (1 - kS D) < D.m - D.u := by
      rw [← h1k]; exact mul_lt_mul_of_pos_right hAP hkS1
    have hneg : ∀ Q, qhat * (1 + α) ≤ Q → A * (1 - F Q) - (D.m - D.u) < 0 := by
      intro Q hQ
      rw [← hl, hqhatl] at hQ
      have h1 : F Qcc ≤ F Q := hΘ.monotone hQ
      rw [hQcc] at h1
      have : A * (1 - F Q) ≤ A * (1 - kS D) :=
        mul_le_mul_of_nonneg_left (by linarith only [h1]) hA0.le
      linarith only [this, hAk]
    have einc : ∀ Q Q', qhat * (1 + α) ≤ Q → Q ≤ Q' →
        emProfit D ν c ω qhat Q' - emProfit D ν c ω qhat Q ≤
          (Q' - Q) * (A * (1 - F Q) - (D.m - D.u)) := by
      intro Q Q' hQ hQQ
      unfold emProfit
      have h1 := clip_bound hid (ν := ν) (hlo.trans hQ) hQQ
      rw [← hA]
      have h2 := mul_le_mul_of_nonneg_left h1 hA0.le
      rw [← hF] at h2
      have e : A * ∫ μ, clip μ (qhat * (1 - ω)) Q' ∂ν - (D.m - D.u) * Q' -
          (A * ∫ μ, clip μ (qhat * (1 - ω)) Q ∂ν - (D.m - D.u) * Q) =
          A * (∫ μ, clip μ (qhat * (1 - ω)) Q' ∂ν - ∫ μ, clip μ (qhat * (1 - ω)) Q ∂ν)
            - (D.m - D.u) * (Q' - Q) := by ring
      rw [e]
      have e2 : (Q' - Q) * (A * (1 - F Q) - (D.m - D.u)) =
          A * ((Q' - Q) * (1 - F Q)) - (D.m - D.u) * (Q' - Q) := by ring
      rw [e2]
      linarith only [h2]
    intro Q hQ
    constructor
    · intro hmax
      by_contra hne
      have hlt : qhat * (1 + α) < Q := lt_of_le_of_ne hQ (Ne.symm hne)
      have h1 := einc _ Q le_rfl hQ
      have h2 := hneg _ le_rfl
      have h3 : emProfit D ν c ω qhat (qhat * (1 + α)) ≤ emProfit D ν c ω qhat Q :=
        isMaxOn_iff.1 hmax _ (Set.mem_Ici.2 le_rfl)
      have : (Q - qhat * (1 + α)) * (A * (1 - F (qhat * (1 + α))) - (D.m - D.u)) < 0 :=
        mul_neg_of_pos_of_neg (by linarith only [hlt]) h2
      linarith only [h1, h3, this]
    · rintro rfl
      refine isMaxOn_iff.2 fun Q' hQ' => ?_
      have hQ' : qhat * (1 + α) ≤ Q' := hQ'
      have h1 := einc _ Q' le_rfl hQ'
      have h2 := hneg _ le_rfl
      have : (Q' - qhat * (1 + α)) * (A * (1 - F (qhat * (1 + α))) - (D.m - D.u)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith only [hQ']) h2.le
      linarith only [h1, this]
  · -- clause 3
    have hq1 : qhat * (1 + α) = Qcc := by rw [← hl]; exact hqhatl
    exact (system_profit_eq_cc D ν hΘ hΘd hν c α ω hω0 hω1.le hα qhat hqhat0.le Qcc
      hQcc).2 hq1
