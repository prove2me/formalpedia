-- Prove2me | solution 1 for PersPricingDist.PersonalA.pu_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T18:50:46.373308+00:00
-- url     : https://prove2.me/submissions/d887a21b-af5b-49e3-a4d2-86b970b77b0e

import Mathlib
import Definitions.Def_PersPricingDist_PersonalA_Setting

open PersPricingDist.PersonalA

namespace PPDAPUCutAux

theorem EF_lin (a b c d : ℝ) :
    ∫ x in c..d, (a - b * x) = a * (d - c) - b * (d ^ 2 - c ^ 2) / 2 := by
  rw [intervalIntegral.integral_sub (by simp) (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_const_mul]
  simp [integral_id]
  ring

lemma uA_of_le (M : Model) {x : ℝ} (hx : x ≤ 1) : M.uA x = 1 - x := by
  unfold Model.uA; exact max_eq_left (by linarith)

lemma uA_of_ge (M : Model) {x : ℝ} (hx : 1 ≤ x) : M.uA x = 0 := by
  unfold Model.uA; exact max_eq_right (by linarith)

lemma uB_of_le (M : Model) {x : ℝ} (hx : M.s * x ≤ M.v) : M.uB x = M.v - M.s * x := by
  unfold Model.uB; exact max_eq_left (by linarith)

lemma uB_of_ge (M : Model) {x : ℝ} (hx : M.v ≤ M.s * x) : M.uB x = 0 := by
  unfold Model.uB; exact max_eq_right (by linarith)

lemma uA_nonneg (M : Model) (x : ℝ) : 0 ≤ M.uA x := by unfold Model.uA; exact le_max_right _ _
lemma uB_nonneg (M : Model) (x : ℝ) : 0 ≤ M.uB x := by unfold Model.uB; exact le_max_right _ _

lemma uA_cont (M : Model) : Continuous M.uA := by unfold Model.uA; fun_prop
lemma uB_cont (M : Model) : Continuous M.uB := by unfold Model.uB; fun_prop

lemma uA_int (M : Model) (a b : ℝ) : IntervalIntegrable M.uA MeasureTheory.volume a b :=
  (uA_cont M).intervalIntegrable a b

/-- Tail of the direct-channel value when the lower limit is at least `1`. -/
lemma tail_ge (M : Model) {p X : ℝ} (hp : 1 ≤ p) (hpX : p ≤ X) : ∫ x in p..X, M.uA x = 0 := by
  have : ∫ x in p..X, M.uA x = ∫ x in p..X, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hpX] at hx
    exact uA_of_ge M (by linarith [hx.1])
  rw [this]; simp

lemma tail_le (M : Model) {p X : ℝ} (hp : p ≤ 1) (hX : 1 ≤ X) :
    ∫ x in p..X, M.uA x = (1 - p) ^ 2 / 2 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (uA_int M p 1) (uA_int M 1 X),
    tail_ge M le_rfl hX]
  have : ∫ x in p..1, M.uA x = ∫ x in p..1, (1 - 1 * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hp] at hx
    rw [uA_of_le M hx.2]; ring
  rw [this, EF_lin]; ring

lemma monoP_eq (M : Model) (hM : M.Standing) : M.monoP = 1 / 2 := by
  have h1 : 1 ≤ M.v / M.s := by rw [le_div_iff₀ hM.s_pos]; linarith [hM.s_lt_v]
  unfold Model.monoP
  rw [tail_le M (by norm_num) (h1.trans hM.X_large)]
  norm_num

/-- A quadratic which is `≤ 0` at `0`, `< 0` at `Y`, and increasing at `Y` is `≤ 0` on `(0,Y)`. -/
lemma quad_nonpos {c2 c1 c0 Y y : ℝ} (hy0 : 0 < y) (hyY : y < Y) (hc0 : c0 ≤ 0)
    (hfY : c2 * Y ^ 2 + c1 * Y + c0 < 0) (hd : 0 < c1 + 2 * c2 * Y) :
    c2 * y ^ 2 + c1 * y + c0 ≤ 0 := by
  by_cases hc2 : c2 ≤ 0
  · have hid : c2 * y ^ 2 + c1 * y + c0 - (c2 * Y ^ 2 + c1 * Y + c0)
        = (y - Y) * ((c1 + 2 * c2 * Y) + c2 * (y - Y)) := by ring
    have h3 : 0 < (c1 + 2 * c2 * Y) + c2 * (y - Y) := by
      have : 0 ≤ c2 * (y - Y) := mul_nonneg_of_nonpos_of_nonpos hc2 (by linarith)
      linarith
    have : (y - Y) * ((c1 + 2 * c2 * Y) + c2 * (y - Y)) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) h3
    linarith
  · push Not at hc2
    have hYpos : 0 < Y := by linarith
    have hid : Y * (c2 * y ^ 2 + c1 * y + c0)
        = (Y - y) * c0 + y * (c2 * Y ^ 2 + c1 * Y + c0) - c2 * Y * y * (Y - y) := by ring
    have t1 : (Y - y) * c0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hc0
    have t2 : y * (c2 * Y ^ 2 + c1 * Y + c0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hy0.le hfY.le
    have t3 : 0 ≤ c2 * Y * y * (Y - y) := by
      have := mul_pos (mul_pos hc2 hYpos) hy0
      exact mul_nonneg this.le (by linarith)
    have : Y * (c2 * y ^ 2 + c1 * y + c0) ≤ 0 := by rw [hid]; linarith
    by_contra hc; push Not at hc
    have := mul_pos hYpos hc
    linarith

lemma revPU_buy (M : Model) {w pB x : ℝ} (h : M.buysBPU w pB x) : M.revPU w pB x = pB := by
  unfold Model.revPU; rw [if_pos h]

lemma revPU_A (M : Model) {w pB x : ℝ} (h : ¬ M.buysBPU w pB x)
    (h2 : 0 < M.uB x ∧ pB ≤ M.uB x) : M.revPU w pB x = M.uA x - M.uB x + pB := by
  unfold Model.revPU; rw [if_neg h, if_pos h2]

lemma revPU_N (M : Model) {w pB x : ℝ} (h2 : ¬ (0 < M.uB x ∧ pB ≤ M.uB x)) :
    M.revPU w pB x = M.uA x := by
  have h : ¬ M.buysBPU w pB x := fun hb => h2 ⟨hb.1, hb.2.1⟩
  unfold Model.revPU; rw [if_neg h, if_neg h2]

lemma revPU_le (M : Model) {w pB x : ℝ} (h : ¬ M.buysBPU w pB x) : M.revPU w pB x ≤ M.uA x := by
  by_cases h2 : 0 < M.uB x ∧ pB ≤ M.uB x
  · rw [revPU_A M h h2]; linarith [h2.2]
  · rw [revPU_N M h2]

lemma revPU_meas (M : Model) (w pB : ℝ) : Measurable (M.revPU w pB) := by
  have hA : Measurable M.uA := (uA_cont M).measurable
  have hB : Measurable M.uB := (uB_cont M).measurable
  have hf : Measurable (fun x => M.uA x - M.uB x + pB) := by fun_prop
  have hS : MeasurableSet {x | M.buysBPU w pB x} := by
    unfold Model.buysBPU
    exact (measurableSet_lt measurable_const hB).inter
      ((measurableSet_le measurable_const hB).inter (measurableSet_le hf measurable_const))
  have hT : MeasurableSet {x | 0 < M.uB x ∧ pB ≤ M.uB x} :=
    (measurableSet_lt measurable_const hB).inter (measurableSet_le measurable_const hB)
  unfold Model.revPU
  exact Measurable.ite hS measurable_const (Measurable.ite hT hf hA)

lemma revPU_bound (M : Model) (w pB x : ℝ) : |M.revPU w pB x| ≤ |pB| + M.uA x + M.uB x := by
  have hA := uA_nonneg M x
  have hB := uB_nonneg M x
  by_cases h : M.buysBPU w pB x
  · rw [revPU_buy M h]; linarith [le_abs_self pB, neg_abs_le pB]
  · by_cases h2 : 0 < M.uB x ∧ pB ≤ M.uB x
    · rw [revPU_A M h h2]
      rw [abs_le]; constructor <;> linarith [le_abs_self pB, neg_abs_le pB]
    · rw [revPU_N M h2, abs_of_nonneg hA]; linarith [abs_nonneg pB]

lemma revPU_int (M : Model) (w pB a b : ℝ) :
    IntervalIntegrable (M.revPU w pB) MeasureTheory.volume a b := by
  have hg : IntervalIntegrable (fun x => |pB| + M.uA x + M.uB x) MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    have := uA_cont M; have := uB_cont M
    fun_prop
  refine hg.mono_fun' (revPU_meas M w pB).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  simpa [Real.norm_eq_abs] using revPU_bound M w pB x

/-- B's buyers when `pB > w ≥ 0`. -/
lemma buys_iff (M : Model) (hM : M.Standing) {w pB x : ℝ} (hw : 0 ≤ w) (hp : w < pB) :
    M.buysBPU w pB x ↔ (1 - M.v + pB - w ≤ (1 - M.s) * x ∧ M.s * x ≤ M.v - pB) := by
  obtain ⟨hs, hsv, hv1, hX⟩ := hM
  unfold Model.buysBPU
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hsx : M.s * x < M.v := by
      by_contra hc; push Not at hc
      rw [uB_of_ge M hc] at h1; exact lt_irrefl _ h1
    rw [uB_of_le M hsx.le] at h2 h3
    refine ⟨?_, by linarith⟩
    by_cases hx : x ≤ 1
    · rw [uA_of_le M hx] at h3; linarith
    · push Not at hx
      have : M.s * 1 < M.s * x := mul_lt_mul_of_pos_left hx hs
      nlinarith
  · rintro ⟨h1, h2⟩
    have hsx : M.s * x ≤ M.v := by linarith
    rw [uB_of_le M hsx]
    refine ⟨by linarith, by linarith, ?_⟩
    by_cases hx : x ≤ 1
    · rw [uA_of_le M hx]; linarith
    · push Not at hx
      rw [uA_of_ge M hx.le]; linarith

lemma demand_eq (M : Model) (hM : M.Standing) {w pB : ℝ} (hw : 0 ≤ w) (hp : w < pB) :
    M.demandBPU w pB = max ((M.v - pB) / M.s - (1 - M.v + pB - w) / (1 - M.s)) 0 := by
  have hs := hM.s_pos
  have hsv := hM.s_lt_v
  have hv1 := hM.v_lt_one
  have hX := hM.X_large
  have h1s : 0 < 1 - M.s := by linarith
  have hlo : 0 ≤ (1 - M.v + pB - w) / (1 - M.s) := div_nonneg (by linarith) h1s.le
  have hup : (M.v - pB) / M.s ≤ M.X := by
    have : (M.v - pB) / M.s ≤ M.v / M.s := div_le_div_of_nonneg_right (by linarith) hs.le
    linarith
  have hset : {x : ℝ | x ∈ Set.Icc 0 M.X ∧ M.buysBPU w pB x} =
      Set.Icc ((1 - M.v + pB - w) / (1 - M.s)) ((M.v - pB) / M.s) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    rw [buys_iff M hM hw hp, div_le_iff₀ h1s, le_div_iff₀ hs]
    constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      have hx0 : 0 ≤ x := le_trans hlo ((div_le_iff₀ h1s).mpr (by linarith))
      have hxX : x ≤ M.X := le_trans ((le_div_iff₀ hs).mpr (by linarith)) hup
      exact ⟨⟨hx0, hxX⟩, by linarith, by linarith⟩
  unfold Model.demandBPU
  rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal']

/-- Profit for `pB > w`. -/
lemma prof_eq (M : Model) (hM : M.Standing) {w pB : ℝ} (hw : 0 ≤ w) (hp : w < pB) :
    M.profBPU w pB = (pB - w) * max ((M.v - M.s + M.s * w - pB) / (M.s * (1 - M.s))) 0 := by
  have hs := hM.s_pos
  have h1s : 0 < 1 - M.s := by linarith [hM.s_lt_v, hM.v_lt_one]
  unfold Model.profBPU
  rw [demand_eq M hM hw hp]
  congr 2
  field_simp
  ring

lemma prof_nonpos (M : Model) {w pB : ℝ} (hp : pB ≤ w) : M.profBPU w pB ≤ 0 := by
  unfold Model.profBPU
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) ENNReal.toReal_nonneg

lemma prof_le_star (M : Model) (hM : M.Standing) {w : ℝ} (hw : 0 ≤ w) (q : ℝ) :
    M.profBPU w q ≤ (M.v - M.s + M.s * w - w) ^ 2 / (4 * (M.s * (1 - M.s))) := by
  have hs := hM.s_pos
  have h1s : 0 < 1 - M.s := by linarith [hM.s_lt_v, hM.v_lt_one]
  have hd : 0 < M.s * (1 - M.s) := mul_pos hs h1s
  have hrhs : 0 ≤ (M.v - M.s + M.s * w - w) ^ 2 / (4 * (M.s * (1 - M.s))) := by positivity
  rcases le_or_gt q w with hq | hq
  · linarith [prof_nonpos M hq]
  · rw [prof_eq M hM hw hq]
    rcases le_or_gt ((M.v - M.s + M.s * w - q) / (M.s * (1 - M.s))) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h.le, mul_div_assoc', div_le_div_iff₀ hd (by positivity)]
      nlinarith [sq_nonneg (2 * q - w - (M.v - M.s + M.s * w)), hd]

lemma prof_star (M : Model) (hM : M.Standing) {w : ℝ} (hw : 0 ≤ w)
    (hwu : w * (1 - M.s) < M.v - M.s) :
    M.profBPU w ((w + (M.v - M.s + M.s * w)) / 2)
      = (M.v - M.s + M.s * w - w) ^ 2 / (4 * (M.s * (1 - M.s))) := by
  have hs := hM.s_pos
  have h1s : 0 < 1 - M.s := by linarith [hM.s_lt_v, hM.v_lt_one]
  have hd : 0 < M.s * (1 - M.s) := mul_pos hs h1s
  rw [prof_eq M hM hw (by linarith)]
  rw [max_eq_left (div_nonneg (by linarith) hd.le)]
  field_simp
  ring

/-- With `w < û`, B's global best response is unique. -/
lemma maximizer_eq (M : Model) (hM : M.Standing) {w pB : ℝ} (hw : 0 ≤ w)
    (hwu : w * (1 - M.s) < M.v - M.s) (hmax : IsMaxOn (M.profBPU w) Set.univ pB) :
    pB = (w + (M.v - M.s + M.s * w)) / 2 := by
  have hs := hM.s_pos
  have h1s : 0 < 1 - M.s := by linarith [hM.s_lt_v, hM.v_lt_one]
  have hd : 0 < M.s * (1 - M.s) := mul_pos hs h1s
  have h1 := isMaxOn_iff.mp hmax ((w + (M.v - M.s + M.s * w)) / 2) (Set.mem_univ _)
  rw [prof_star M hM hw hwu] at h1
  have hpos : 0 < (M.v - M.s + M.s * w - w) ^ 2 / (4 * (M.s * (1 - M.s))) := by
    have : 0 < M.v - M.s + M.s * w - w := by linarith
    positivity
  rcases le_or_gt pB w with hp | hp
  · linarith [prof_nonpos M hp]
  · rw [prof_eq M hM hw hp] at h1
    rcases le_or_gt ((M.v - M.s + M.s * w - pB) / (M.s * (1 - M.s))) 0 with h | h
    · rw [max_eq_right h] at h1; linarith
    · rw [max_eq_left h.le, mul_div_assoc', div_le_div_iff₀ (by positivity) hd] at h1
      have : (2 * pB - w - (M.v - M.s + M.s * w)) ^ 2 ≤ 0 := by nlinarith
      have : 2 * pB - w - (M.v - M.s + M.s * w) = 0 := by nlinarith [sq_nonneg (2 * pB - w - (M.v - M.s + M.s * w))]
      linarith

/-- Industry profit at B's best response, for `0 ≤ w < û`. -/
lemma indPU_star (M : Model) (hM : M.Standing) {w : ℝ} (hw : 0 ≤ w)
    (hwu : w * (1 - M.s) < M.v - M.s) :
    let p := (w + (M.v - M.s + M.s * w)) / 2
    M.indPU w p =
      (∫ x in (0:ℝ)..((1 - M.v + p - w) / (1 - M.s)), ((1 - M.v + p) - (1 - M.s) * x)) +
      (∫ x in ((1 - M.v + p - w) / (1 - M.s))..((M.v - p) / M.s), (p - 0 * x)) +
      (∫ x in ((M.v - p) / M.s)..M.X, M.uA x) := by
  intro p
  have hs := hM.s_pos
  have hsv := hM.s_lt_v
  have hv1 := hM.v_lt_one
  have hX := hM.X_large
  have h1s : 0 < 1 - M.s := by linarith
  have hpw : w < p := by simp only [p]; linarith
  set lo := (1 - M.v + p - w) / (1 - M.s) with hlo
  set up := (M.v - p) / M.s with hup
  have hlom : lo * (1 - M.s) = 1 - M.v + p - w := by rw [hlo]; field_simp
  have hupm : M.s * up = M.v - p := by rw [hup]; field_simp
  have hlo0 : 0 ≤ lo := div_nonneg (by linarith) h1s.le
  have hlo1 : lo ≤ 1 := by
    rw [hlo, div_le_one h1s]; simp only [p]; nlinarith
  have hloup : lo ≤ up := by
    rw [hlo, hup, div_le_div_iff₀ h1s hs]; simp only [p]; nlinarith
  have hupX : up ≤ M.X := by
    have : up ≤ M.v / M.s := div_le_div_of_nonneg_right (by linarith) hs.le
    linarith
  have hI := revPU_int M w p
  unfold Model.indPU
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 lo) (hI lo M.X),
    ← intervalIntegral.integral_add_adjacent_intervals (hI lo up) (hI up M.X)]
  have e1 : ∫ x in (0:ℝ)..lo, M.revPU w p x = ∫ x in (0:ℝ)..lo, ((1 - M.v + p) - (1 - M.s) * x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume lo] with x hne hx
    rw [Set.uIoc_of_le hlo0] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hxl : x < lo := lt_of_le_of_ne hx2 hne
    have hnb : ¬ M.buysBPU w p x := by
      rw [buys_iff M hM hw hpw]
      rintro ⟨h1, _⟩
      have := mul_lt_mul_of_pos_right hxl h1s
      nlinarith
    have hsx : M.s * x ≤ M.v - p := by
      have := mul_le_mul_of_nonneg_left (hxl.le.trans hloup) hs.le; linarith
    have hB := uB_of_le M (show M.s * x ≤ M.v by linarith)
    rw [revPU_A M hnb (by rw [hB]; constructor <;> linarith), hB, uA_of_le M (by linarith)]
    ring
  have e2 : ∫ x in lo..up, M.revPU w p x = ∫ x in lo..up, (p - 0 * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hloup] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hb : M.buysBPU w p x := by
      rw [buys_iff M hM hw hpw]
      constructor
      · have := mul_le_mul_of_nonneg_right hx1 h1s.le; linarith
      · have := mul_le_mul_of_nonneg_left hx2 hs.le; linarith
    simp only [revPU_buy M hb]; ring
  have e3 : ∫ x in up..M.X, M.revPU w p x = ∫ x in up..M.X, M.uA x := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le hupX] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hsx : M.v - p < M.s * x := by
      have := mul_lt_mul_of_pos_left hx1 hs; linarith
    apply revPU_N
    rintro ⟨h1, h2⟩
    by_cases hc : M.s * x ≤ M.v
    · rw [uB_of_le M hc] at h2; linarith
    · push Not at hc; rw [uB_of_ge M hc.le] at h1; exact lt_irrefl _ h1
  rw [e1, e2, e3]
  ring

/-- For `w ≥ û`, no maximizing retail price gives a gain over mono distribution. -/
lemma indPU_le_high (M : Model) (hM : M.Standing) {w pB : ℝ} (hw : 0 ≤ w)
    (hwu : M.v - M.s ≤ w * (1 - M.s)) (hmax : IsMaxOn (M.profBPU w) Set.univ pB) :
    M.indPU w pB ≤ M.monoP := by
  have hs := hM.s_pos
  have hsv := hM.s_lt_v
  have hv1 := hM.v_lt_one
  have hX := hM.X_large
  have h1s : 0 < 1 - M.s := by linarith
  have hX0 : 0 ≤ M.X := by
    have : 0 ≤ M.v / M.s := div_nonneg (by linarith) hs.le
    linarith
  have hwpos : 0 < w := by
    have : 0 < w * (1 - M.s) := by linarith
    exact pos_of_mul_pos_left this h1s.le
  unfold Model.indPU Model.monoP
  rcases lt_trichotomy pB w with hp | hp | hp
  · -- zero demand
    have h1 := isMaxOn_iff.mp hmax w (Set.mem_univ _)
    have h0 : M.profBPU w w = 0 := by unfold Model.profBPU; simp
    rw [h0] at h1
    have hd : M.demandBPU w pB = 0 := by
      unfold Model.profBPU at h1
      have hnn : 0 ≤ M.demandBPU w pB := ENNReal.toReal_nonneg
      by_contra hne
      have : 0 < M.demandBPU w pB := lt_of_le_of_ne hnn (Ne.symm hne)
      have := mul_neg_of_neg_of_pos (by linarith : pB - w < 0) this
      linarith
    have hfin : MeasureTheory.volume {x : ℝ | x ∈ Set.Icc 0 M.X ∧ M.buysBPU w pB x} ≠ ⊤ := by
      apply ne_top_of_le_ne_top (b := MeasureTheory.volume (Set.Icc (0:ℝ) M.X))
      · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
      · exact MeasureTheory.measure_mono (fun x hx => hx.1)
    have hzero : MeasureTheory.volume {x : ℝ | x ∈ Set.Icc 0 M.X ∧ M.buysBPU w pB x} = 0 := by
      unfold Model.demandBPU at hd
      rcases (ENNReal.toReal_eq_zero_iff _).mp hd with h | h
      · exact h
      · exact absurd h hfin
    apply intervalIntegral.integral_mono_ae_restrict hX0 (revPU_int M w pB 0 M.X) (uA_int M 0 M.X)
    have hae : ∀ᵐ x ∂MeasureTheory.volume, x ∉ {x : ℝ | x ∈ Set.Icc 0 M.X ∧ M.buysBPU w pB x} :=
      MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hzero
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hae] with x hx hxI
    apply revPU_le
    intro hb; exact hx ⟨hxI, hb⟩
  · subst hp
    apply intervalIntegral.integral_mono_on hX0 (revPU_int M pB pB 0 M.X) (uA_int M 0 M.X)
    intro x _
    by_cases hb : M.buysBPU pB pB x
    · rw [revPU_buy M hb]
      obtain ⟨h1, h2, h3⟩ := hb
      have hsx : M.s * x ≤ M.v := by
        by_contra hc; push Not at hc
        rw [uB_of_ge M hc.le] at h1; exact lt_irrefl _ h1
      have hB := uB_of_le M hsx
      have key : M.uB x ≤ M.uA x := by
        rw [hB] at h2 ⊢
        have h2' : M.v - M.s ≤ (1 - M.s) * (M.v - M.s * x) := by nlinarith
        have h3' : (1 - M.s) * x ≤ 1 - M.v := by nlinarith
        have : 1 - x ≤ M.uA x := le_max_left _ _
        nlinarith
      linarith
    · exact revPU_le M hb
  · apply intervalIntegral.integral_mono_on hX0 (revPU_int M w pB 0 M.X) (uA_int M 0 M.X)
    intro x _
    apply revPU_le
    rw [buys_iff M hM hw hp]
    rintro ⟨h1, h2⟩
    have := mul_le_mul_of_nonneg_left h1 hs.le
    have := mul_le_mul_of_nonneg_left h2 h1s.le
    nlinarith

noncomputable def Rf (s : ℝ) : ℝ := (1 - s) * (2 + 5 * s + s ^ 2) / (1 + 2 * s)
noncomputable def Qf (s v : ℝ) : ℝ := ((1 + s) * v - 2 * s) ^ 2 - s ^ 2 * Rf s
noncomputable def wS (s v : ℝ) : ℝ := s * (s + v + 2) / (s ^ 2 + 5 * s + 2)
noncomputable def GAf (s v w : ℝ) : ℝ :=
  (2 * s + 1) * Qf s v / (2 * s * (1 - s) * (1 + s) * (s ^ 2 + 5 * s + 2))
    - (s ^ 2 + 5 * s + 2) / (8 * s) * (w - wS s v) ^ 2
def PBf (s v w : ℝ) : ℝ :=
  s^4*w^2 - 2*s^4*w + s^4 - 2*s^3*v*w + 2*s^3*v + 3*s^3*w^2 - 4*s^3*w + s^3 + s^2*v^2
    + 4*s^2*v*w - 6*s^2*v - 4*s^2*w^2 + 4*s^2*w + s^2 + s*v^2 - 2*s*v - s*w^2 + 2*s*w + v^2
    - 2*v*w + w^2

lemma gainA_id (s v w : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (let p := (w + (v - s + s * w)) / 2
     ((1 - v + p) * ((1 - v + p - w) / (1 - s) - 0) - (1 - s) * (((1 - v + p - w) / (1 - s)) ^ 2 - 0 ^ 2) / 2)
     + (p * ((v - p) / s - (1 - v + p - w) / (1 - s)) - 0 * (((v - p) / s) ^ 2 - ((1 - v + p - w) / (1 - s)) ^ 2) / 2)
     - 1 / 2) = GAf s v w := by
  dsimp only
  unfold GAf Qf Rf wS
  have h1 : (1 - s) ≠ 0 := by linarith
  have h2 : (1 + 2 * s) ≠ 0 := by linarith
  have h3 : (s ^ 2 + 5 * s + 2) ≠ 0 := by nlinarith
  have h4 : (1 + s) ≠ 0 := by linarith
  have h5 : s ≠ 0 := hs.ne'
  field_simp
  ring

lemma gainB_id (s v w : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    GAf s v w + (1 - (v - (w + (v - s + s * w)) / 2) / s) ^ 2 / 2
      = PBf s v w / (8 * s ^ 2 * (1 - s)) := by
  unfold GAf Qf Rf wS PBf
  have h1 : (1 - s) ≠ 0 := by linarith
  have h2 : (1 + 2 * s) ≠ 0 := by linarith
  have h3 : (s ^ 2 + 5 * s + 2) ≠ 0 := by nlinarith
  have h4 : (1 + s) ≠ 0 := by linarith
  have h5 : s ≠ 0 := hs.ne'
  field_simp
  ring

lemma GAf_le (s v w : ℝ) (hs : 0 < s) (hs1 : s < 1) (hQ : Qf s v ≤ 0) : GAf s v w ≤ 0 := by
  unfold GAf
  have h1 : (2 * s + 1) * Qf s v / (2 * s * (1 - s) * (1 + s) * (s ^ 2 + 5 * s + 2)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith
    · have : 0 < 1 - s := by linarith
      positivity
  have h2 : 0 ≤ (s ^ 2 + 5 * s + 2) / (8 * s) * (w - wS s v) ^ 2 := by positivity
  linarith

lemma caseB (s v w : ℝ) (hs : 0 < s) (hs1 : s < 1) (hv : s < v) (hv1 : v < 1)
    (hQ : Qf s v ≤ 0) (hw1 : v - s < (1 + s) * w) (hw2 : w * (1 - s) < v - s) :
    PBf s v w ≤ 0 := by
  have h1 : (1 - s) ≠ 0 := by linarith
  have h4 : (1 + s) ≠ 0 := by linarith
  have h1s : 0 < 1 - s := by linarith
  set c2 := (s - 1) * (s ^ 3 + 4 * s ^ 2 - 1)
  set c1 := -4 * s * (s - 1) * (s ^ 3 + 4 * s ^ 2 - 2 * s * v + 2 * s - v) / (s + 1)
  set c0 := 4 * s ^ 2 * (s ^ 4 + 3 * s ^ 3 - 4 * s ^ 2 * v + 2 * s * v ^ 2 - 2 * s * v - s + v ^ 2)
    / (s + 1) ^ 2
  set Y := 2 * s * (v - s) / ((1 - s) * (1 + s))
  set y := w - (v - s) / (1 + s)
  have hP : PBf s v w = c2 * y ^ 2 + c1 * y + c0 := by
    simp only [c2, c1, c0, y]; unfold PBf
    have : (s + 1) ≠ 0 := by linarith
    field_simp; ring
  have hfY : c2 * Y ^ 2 + c1 * Y + c0 = -(4 * s ^ 3 * (1 - v) ^ 2) / (1 - s) := by
    simp only [c2, c1, c0, Y]
    have : (s + 1) ≠ 0 := by linarith
    field_simp; ring
  have hd : c1 + 2 * c2 * Y = 4 * s ^ 2 * (1 + s) * (1 - v) := by
    simp only [c2, c1, Y]
    have : (s + 1) ≠ 0 := by linarith
    field_simp; ring
  have hc0 : c0 = 8 * s ^ 2 * (1 - s) * GAf s v ((v - s) / (1 + s)) := by
    simp only [c0]; unfold GAf Qf Rf wS
    have h2 : (1 + 2 * s) ≠ 0 := by linarith
    have h3 : (s ^ 2 + 5 * s + 2) ≠ 0 := by nlinarith
    have : (s + 1) ≠ 0 := by linarith
    have h5 : s ≠ 0 := hs.ne'
    field_simp; ring
  rw [hP]
  apply quad_nonpos (Y := Y)
  · simp only [y]; rw [sub_pos, div_lt_iff₀ (by linarith)]; linarith
  · simp only [y, Y]
    rw [show (2 * s * (v - s) / ((1 - s) * (1 + s))) = (v - s) / (1 - s) - (v - s) / (1 + s) by
      field_simp; ring]
    have : w < (v - s) / (1 - s) := by rw [lt_div_iff₀ h1s]; linarith
    linarith
  · rw [hc0]
    have := GAf_le s v ((v - s) / (1 + s)) hs hs1 hQ
    have : 0 ≤ 8 * s ^ 2 * (1 - s) := by positivity
    nlinarith
  · rw [hfY]; apply div_neg_of_neg_of_pos _ h1s
    have : 0 < 4 * s ^ 3 * (1 - v) ^ 2 := by
      have : 0 < 1 - v := by linarith
      positivity
    linarith
  · rw [hd]
    have : 0 < 1 - v := by linarith
    positivity

end PPDAPUCutAux

open PPDAPUCutAux in
theorem solution (M : Model) (hM : M.Standing) :
    M.DualPU ↔ Model.vCheck M.s < M.v := by
  have hs := hM.s_pos
  have hsv := hM.s_lt_v
  have hv1 := hM.v_lt_one
  have hX := hM.X_large
  have h1s : 0 < 1 - M.s := by linarith
  have h1v : 1 ≤ M.v / M.s := by rw [le_div_iff₀ hs]; linarith
  have hX1 : 1 ≤ M.X := h1v.trans hX
  have hR0 : 0 ≤ Rf M.s := by
    unfold Rf; apply div_nonneg (mul_nonneg h1s.le (by positivity)) (by linarith)
  have hq2 : Real.sqrt (Rf M.s) ^ 2 = Rf M.s := Real.sq_sqrt hR0
  have hq0 : 0 ≤ Real.sqrt (Rf M.s) := Real.sqrt_nonneg _
  have hRge : (1 - M.s) ^ 2 ≤ Rf M.s := by
    unfold Rf; rw [le_div_iff₀ (by linarith)]; nlinarith
  have hq1 : 1 - M.s ≤ Real.sqrt (Rf M.s) := by nlinarith
  have hvc : Model.vCheck M.s < M.v ↔ M.s * (2 + Real.sqrt (Rf M.s)) < M.v * (1 + M.s) := by
    unfold Model.vCheck Rf; rw [div_lt_iff₀ (by linarith)]
  have hQf : Qf M.s M.v = ((1 + M.s) * M.v - 2 * M.s - M.s * Real.sqrt (Rf M.s))
      * ((1 + M.s) * M.v - 2 * M.s + M.s * Real.sqrt (Rf M.s)) := by
    unfold Qf; linear_combination M.s ^ 2 * hq2
  have gain : ∀ w, 0 ≤ w → w * (1 - M.s) < M.v - M.s →
      M.indPU w ((w + (M.v - M.s + M.s * w)) / 2) - 1 / 2 = GAf M.s M.v w
        + ∫ x in ((M.v - (w + (M.v - M.s + M.s * w)) / 2) / M.s)..M.X, M.uA x := by
    intro w hw0 hwu
    rw [indPU_star M hM hw0 hwu, EF_lin, EF_lin, ← gainA_id M.s M.v w hs (by linarith)]
    ring
  have hupX : ∀ w, 0 ≤ w → (M.v - (w + (M.v - M.s + M.s * w)) / 2) / M.s ≤ M.X := by
    intro w hw0
    have : (M.v - (w + (M.v - M.s + M.s * w)) / 2) / M.s ≤ M.v / M.s :=
      div_le_div_of_nonneg_right (by nlinarith) hs.le
    linarith
  unfold Model.DualPU
  rw [monoP_eq M hM, hvc]
  constructor
  · rintro ⟨w, hw0, pB, hmax, hgain⟩
    by_contra hcon
    push Not at hcon
    have hQ : Qf M.s M.v ≤ 0 := by
      rw [hQf]
      apply mul_nonpos_of_nonpos_of_nonneg
      · linarith
      · nlinarith
    rcases le_or_gt (M.v - M.s) (w * (1 - M.s)) with hhi | hlo
    · have := indPU_le_high M hM hw0 hhi hmax
      rw [monoP_eq M hM] at this; linarith
    · have hp := maximizer_eq M hM hw0 hlo hmax
      subst hp
      have hg := gain w hw0 hlo
      rcases le_or_gt ((1 + M.s) * w) (M.v - M.s) with hA | hB
      · have hu1 : 1 ≤ (M.v - (w + (M.v - M.s + M.s * w)) / 2) / M.s := by
          rw [le_div_iff₀ hs]; linarith
        rw [tail_ge M hu1 (hupX w hw0)] at hg
        have := GAf_le M.s M.v w hs (by linarith) hQ
        linarith
      · have hu1 : (M.v - (w + (M.v - M.s + M.s * w)) / 2) / M.s ≤ 1 := by
          rw [div_le_iff₀ hs]; linarith
        rw [tail_le M hu1 hX1, gainB_id M.s M.v w hs (by linarith)] at hg
        have hPB := caseB M.s M.v w hs (by linarith) hsv hv1 hQ hB hlo
        have : PBf M.s M.v w / (8 * M.s ^ 2 * (1 - M.s)) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hPB (by positivity)
        linarith
  · intro hcon
    have hQ : 0 < Qf M.s M.v := by
      rw [hQf]
      apply mul_pos
      · linarith
      · nlinarith [mul_nonneg hs.le hq0]
    have hd : 0 < M.s ^ 2 + 5 * M.s + 2 := by positivity
    have hw0 : 0 ≤ wS M.s M.v := by unfold wS; exact div_nonneg (mul_nonneg hs.le (by linarith)) hd.le
    have hwu : wS M.s M.v * (1 - M.s) < M.v - M.s := by
      unfold wS
      rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
      nlinarith [mul_nonneg hs.le hq0]
    refine ⟨wS M.s M.v, hw0, (wS M.s M.v + (M.v - M.s + M.s * wS M.s M.v)) / 2, ?_, ?_⟩
    · rw [isMaxOn_iff]
      intro x _
      rw [prof_star M hM hw0 hwu]
      exact prof_le_star M hM hw0 x
    · have hg := gain _ hw0 hwu
      have htail : 0 ≤ ∫ x in ((M.v - (wS M.s M.v + (M.v - M.s + M.s * wS M.s M.v)) / 2) / M.s)..M.X,
          M.uA x :=
        intervalIntegral.integral_nonneg (hupX _ hw0) (fun x _ => uA_nonneg M x)
      have hGA : 0 < GAf M.s M.v (wS M.s M.v) := by
        unfold GAf
        rw [sub_self]
        have : 0 < (2 * M.s + 1) * Qf M.s M.v / (2 * M.s * (1 - M.s) * (1 + M.s) * (M.s ^ 2 + 5 * M.s + 2)) := by
          apply div_pos (by nlinarith)
          positivity
        simpa using this
      linarith
