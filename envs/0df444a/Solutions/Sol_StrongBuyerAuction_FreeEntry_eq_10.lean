-- Prove2me | solution 1 for StrongBuyerAuction.FreeEntry.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:59:46.551182+00:00
-- url     : https://prove2.me/submissions/617459ee-467f-4ea6-8c37-532731a874f9

import Mathlib
import Definitions.Def_StrongBuyerAuction_FreeEntry_Model

open MeasureTheory ProbabilityTheory Set

namespace SBAHelp

/-- strict comparison of interval integrals over `0..1` -/
lemma intv_lt {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1)
    (hle : ∀ x ∈ Ioo (0:ℝ) 1, f x ≤ g x)
    (S : Set ℝ) (hpos : 0 < volume S) (hS : S ⊆ {x ∈ Ioo (0:ℝ) 1 | f x < g x}) :
    ∫ x in (0:ℝ)..1, f x < ∫ x in (0:ℝ)..1, g x := by
  apply intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero
    zero_le_one hf hg
  · rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall hle)
  · rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    refine (lt_of_lt_of_le hpos ?_).ne'
    refine le_trans (measure_mono ?_) (Measure.le_restrict_apply _ _)
    intro x hx
    exact ⟨(hS hx).2, (hS hx).1⟩

lemma intv_of_bdd {f : ℝ → ℝ} (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    IntervalIntegrable f volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    hf.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hb x)

/-- a function with values in `[0,1]`, measurable -/
def Unit01 (F : ℝ → ℝ) : Prop := Measurable F ∧ ∀ x, 0 ≤ F x ∧ F x ≤ 1

lemma unit_cdf (μ : Measure ℝ) : Unit01 (cdf μ) :=
  ⟨(cdf μ).mono.measurable, fun x => ⟨cdf_nonneg μ x, cdf_le_one μ x⟩⟩

lemma pow_unit {F : ℝ → ℝ} (hF : Unit01 F) {a : ℝ} (ha : 0 ≤ a) :
    Unit01 (fun z => F z ^ a) :=
  ⟨hF.1.pow_const a, fun x => ⟨Real.rpow_nonneg (hF.2 x).1 _,
    Real.rpow_le_one (hF.2 x).1 (hF.2 x).2 ha⟩⟩

lemma unit_mul {F G : ℝ → ℝ} (hF : Unit01 F) (hG : Unit01 G) :
    Unit01 (fun z => F z * G z) :=
  ⟨hF.1.mul hG.1, fun x => ⟨mul_nonneg (hF.2 x).1 (hG.2 x).1,
    mul_le_one₀ (hF.2 x).2 (hG.2 x).1 (hG.2 x).2⟩⟩

lemma one_sub_unit {F : ℝ → ℝ} (hF : Unit01 F) : Unit01 (fun z => 1 - F z) :=
  ⟨measurable_const.sub hF.1, fun x => ⟨by linarith [(hF.2 x).2], by linarith [(hF.2 x).1]⟩⟩

lemma Unit01.intv {F : ℝ → ℝ} (hF : Unit01 F) : IntervalIntegrable F volume 0 1 :=
  intv_of_bdd hF.1 fun x => abs_le.2 ⟨by linarith [(hF.2 x).1], (hF.2 x).2⟩

lemma integrand_unit {F G : ℝ → ℝ} (hF : Unit01 F) (hG : Unit01 G) {N : ℝ} (hN : 1 ≤ N) :
    Unit01 (fun z => (1 - F z) * G z * F z ^ (N - 1)) :=
  unit_mul (unit_mul (one_sub_unit hF) hG) (pow_unit hF (by linarith))

open StrongBuyerAuction.FreeEntry

/-- weak monotonicity of regular-buyer profit in `N` -/
lemma piReg_anti {F G : ℝ → ℝ} (hF : Unit01 F) (hG : Unit01 G) {N N' : ℝ}
    (hN : 1 ≤ N) (hNN' : N ≤ N') : piReg F G N' ≤ piReg F G N := by
  unfold piReg
  apply intervalIntegral.integral_mono_on zero_le_one
    (integrand_unit hF hG (by linarith)).intv (integrand_unit hF hG hN).intv
  intro x _
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith [(hF.2 x).2]) (hG.2 x).1)
  exact Real.rpow_le_rpow_of_exponent_ge' (hF.2 x).1 (hF.2 x).2 (by linarith) (by linarith)

/-- strict monotonicity (Lemma 1, `N` part) -/
lemma piReg_strict_anti {F G : ℝ → ℝ} (hF : Unit01 F) (hG : Unit01 G)
    (hGF : ∀ x ∈ Ioo (0:ℝ) 1, G x ≤ F x)
    (hnd : 0 < volume {x ∈ Ioo (0 : ℝ) 1 | 0 < G x ∧ F x < 1}) {N N' : ℝ}
    (hN : 1 ≤ N) (hNN' : N < N') : piReg F G N' < piReg F G N := by
  unfold piReg
  apply intv_lt (integrand_unit hF hG (by linarith)).intv (integrand_unit hF hG hN).intv
  · intro x _
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith [(hF.2 x).2]) (hG.2 x).1)
    exact Real.rpow_le_rpow_of_exponent_ge' (hF.2 x).1 (hF.2 x).2 (by linarith) (by linarith)
  · exact hnd
  · rintro x ⟨hx, hG0, hF1⟩
    refine ⟨hx, ?_⟩
    have hF0 : 0 < F x := lt_of_lt_of_le hG0 (hGF x hx)
    apply mul_lt_mul_of_pos_left _ (mul_pos (by linarith) hG0)
    exact Real.rpow_lt_rpow_of_exponent_gt hF0 hF1 (by linarith)

/-- Lemma 1, dominance part -/
lemma piReg_dom {F G G' : ℝ → ℝ} (hF : Unit01 F) (hG : Unit01 G) (hG' : Unit01 G')
    (hGF : ∀ x ∈ Ioo (0:ℝ) 1, G x ≤ F x)
    (hG'G : ∀ x ∈ Ioo (0:ℝ) 1, G' x ≤ G x)
    (hguard : 0 < volume {x ∈ Ioo (0 : ℝ) 1 | G' x < G x ∧ F x < 1}) {N : ℝ}
    (hN : 1 ≤ N) : piReg F G' N < piReg F G N := by
  unfold piReg
  apply intv_lt (integrand_unit hF hG' hN).intv (integrand_unit hF hG hN).intv
  · intro x hx
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hF.2 x).1 _)
    exact mul_le_mul_of_nonneg_left (hG'G x hx) (by linarith [(hF.2 x).2])
  · exact hguard
  · rintro x ⟨hx, hlt, hF1⟩
    refine ⟨hx, ?_⟩
    have hF0 : 0 < F x := lt_of_le_of_lt (hG'.2 x).1 (lt_of_lt_of_le hlt (hGF x hx))
    apply mul_lt_mul_of_pos_right _ (Real.rpow_pos_of_pos hF0 _)
    exact mul_lt_mul_of_pos_left hlt (by linarith)

/-- Lemma 2 -/
lemma entry_lt {F G G' : ℝ → ℝ} (hF : Unit01 F) (hG : Unit01 G) (hG' : Unit01 G')
    (hGF : ∀ x ∈ Ioo (0:ℝ) 1, G x ≤ F x)
    (hG'G : ∀ x ∈ Ioo (0:ℝ) 1, G' x ≤ G x)
    (hguard : 0 < volume {x ∈ Ioo (0 : ℝ) 1 | G' x < G x ∧ F x < 1}) {c NG NG' : ℝ}
    (hNG : IsFreeEntry F G c NG) (hNG' : IsFreeEntry F G' c NG') : NG' < NG := by
  by_contra h
  push Not at h
  have h1 := piReg_dom hF hG hG' hGF hG'G hguard hNG'.2
  have h2 := piReg_anti hF hG hNG.2 h
  linarith [hNG.1, hNG'.1]

/-- the key pointwise inequality: `x^a - x^(a+d) > d (1-x) x^(a+d)` on `(0,1)` -/
lemma key_pt {x a d : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hd : 0 < d) :
    d * (1 - x) * x ^ (a + d) < x ^ a - x ^ (a + d) := by
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx0 a
  rw [Real.rpow_add hx0]
  have hlog : Real.log x < x - 1 := Real.log_lt_sub_one_of_pos hx0 hx1.ne
  have hxd : x ^ d = Real.exp (Real.log x * d) := Real.rpow_def_of_pos hx0 d
  have he := Real.add_one_le_exp (-(Real.log x * d))
  have hprod : Real.exp (Real.log x * d) * Real.exp (-(Real.log x * d)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (Real.log x * d) := Real.exp_pos _
  -- x^d * (1 + d(1-x)) < 1
  have hk : x ^ d * (1 + d * (1 - x)) < 1 := by
    rw [hxd]
    have : 1 + d * (1 - x) < -(Real.log x * d) + 1 := by nlinarith
    calc Real.exp (Real.log x * d) * (1 + d * (1 - x))
        < Real.exp (Real.log x * d) * (-(Real.log x * d) + 1) :=
          mul_lt_mul_of_pos_left this hpos
      _ ≤ Real.exp (Real.log x * d) * Real.exp (-(Real.log x * d)) :=
          mul_le_mul_of_nonneg_left he hpos.le
      _ = 1 := hprod
  nlinarith

/-- pointwise comparison for revenue monotonicity -/
lemma rev_pt {F G : ℝ → ℝ} (hF : Unit01 F) (hG : Unit01 G)
    (hGF : ∀ x ∈ Ioo (0:ℝ) 1, G x ≤ F x) {a b : ℝ} (ha : 1 ≤ a) (hab : a < b)
    (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) :
    (b - a) * ((1 - F x) * G x * F x ^ (b - 1)) ≤ F x ^ a - F x ^ b ∧
    (0 < G x → F x < 1 →
      (b - a) * ((1 - F x) * G x * F x ^ (b - 1)) < F x ^ a - F x ^ b) := by
  have hGx := hGF x hx
  obtain ⟨hF0, hF1⟩ := hF.2 x
  have hG0 := (hG.2 x).1
  have strict : 0 < F x → F x < 1 →
      (b - a) * ((1 - F x) * G x * F x ^ (b - 1)) < F x ^ a - F x ^ b := by
    intro h0 h1
    have hk := key_pt (a := a) h0 h1 (sub_pos.2 hab)
    rw [show a + (b - a) = b by ring] at hk
    have hb : F x ^ b = F x * F x ^ (b - 1) := by
      conv_lhs => rw [show b = 1 + (b - 1) by ring]
      rw [Real.rpow_add h0, Real.rpow_one]
    have hpb : 0 ≤ F x ^ (b - 1) := Real.rpow_nonneg hF0 _
    have : (b - a) * ((1 - F x) * G x * F x ^ (b - 1)) ≤ (b - a) * (1 - F x) * F x ^ b := by
      rw [hb]
      have := mul_le_mul_of_nonneg_right hGx
        (mul_nonneg (mul_nonneg (sub_pos.2 hab).le (by linarith : (0:ℝ) ≤ 1 - F x)) hpb)
      nlinarith
    linarith
  refine ⟨?_, fun h0 h1 => strict (lt_of_lt_of_le h0 hGx) h1⟩
  rcases eq_or_lt_of_le hF0 with h | h
  · have hG' : G x = 0 := le_antisymm (h ▸ hGx) hG0
    rw [hG', ← h]
    simp [Real.zero_rpow (show b ≠ 0 by linarith), Real.zero_rpow (show a ≠ 0 by linarith)]
  rcases eq_or_lt_of_le hF1 with h' | h'
  · rw [h']; simp
  exact (strict h h').le

/-- revenue (with `c` frozen) strictly increases on `[1, NG]` -/
lemma rev_mono {F G : ℝ → ℝ} (hF : Unit01 F) (hG : Unit01 G)
    (hGF : ∀ x ∈ Ioo (0:ℝ) 1, G x ≤ F x)
    (hnd : 0 < volume {x ∈ Ioo (0 : ℝ) 1 | 0 < G x ∧ F x < 1}) {c NG : ℝ}
    (hNG : IsFreeEntry F G c NG) :
    StrictMonoOn (fun N : ℝ => 1 - (∫ z in (0 : ℝ)..1, F z ^ N) - N * c) (Icc 1 NG) := by
  intro a ha b hb hab
  simp only
  have hint : (b - a) * piReg F G b < ∫ z in (0:ℝ)..1, (F z ^ a - F z ^ b) := by
    unfold piReg
    rw [← intervalIntegral.integral_const_mul]
    apply intv_lt ((integrand_unit hF hG (by linarith [hb.1])).intv.const_mul _)
      ((pow_unit hF (by linarith [ha.1])).intv.sub (pow_unit hF (by linarith [ha.1])).intv)
    · intro x hx; exact (rev_pt hF hG hGF ha.1 hab x hx).1
    · exact hnd
    · rintro x ⟨hx, h0, h1⟩
      exact ⟨hx, (rev_pt hF hG hGF ha.1 hab x hx).2 h0 h1⟩
  rw [intervalIntegral.integral_sub (pow_unit hF (by linarith [ha.1])).intv
    (pow_unit hF (by linarith [ha.1])).intv] at hint
  have hc : c ≤ piReg F G b := by
    rw [← hNG.1]; exact piReg_anti hF hG (by linarith [hb.1]) hb.2
  have : (b - a) * c ≤ (b - a) * piReg F G b :=
    mul_le_mul_of_nonneg_left hc (sub_pos.2 hab).le
  nlinarith

end SBAHelp

namespace SBAHelp
open StrongBuyerAuction.FreeEntry

lemma powlog_bound {u N : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hN : 1/2 ≤ N) :
    |u ^ N * Real.log u| ≤ 2 := by
  rcases eq_or_lt_of_le hu0 with h | h
  · rw [← h]; simp
  have := Real.abs_log_mul_self_rpow_lt u N h hu1 (by linarith)
  rw [mul_comm]
  have h2 : 1 / N ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  linarith

lemma powlog_deriv {u N : ℝ} (hu0 : 0 ≤ u) (hN : 0 < N) :
    HasDerivAt (fun M : ℝ => u ^ M) (u ^ N * Real.log u) N := by
  rcases eq_or_lt_of_le hu0 with h | h
  · rw [← h, Real.log_zero, mul_zero]
    apply (hasDerivAt_const N (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hN] with M hM
    simp [Real.zero_rpow hM.ne']
  · exact (Real.hasStrictDerivAt_const_rpow h N).hasDerivAt

lemma deriv_part {F : ℝ → ℝ} (hF : Unit01 F) {c NG : ℝ} (hNG : 1 ≤ NG) :
    HasDerivAt (fun N : ℝ => 1 - (∫ z in (0 : ℝ)..1, F z ^ N) - N * c)
      (-(∫ z in (0 : ℝ)..1, F z ^ NG * Real.log (F z)) - c) NG := by
  have hD : HasDerivAt (fun N : ℝ => ∫ z in (0 : ℝ)..1, F z ^ N)
      (∫ z in (0 : ℝ)..1, F z ^ NG * Real.log (F z)) NG := by
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun N z => F z ^ N) (F' := fun N z => F z ^ N * Real.log (F z))
      (bound := fun _ => (2:ℝ)) (s := Metric.ball NG (1/2))
      (Metric.ball_mem_nhds _ (by norm_num)) ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Filter.Eventually.of_forall fun N =>
        (hF.1.pow_const N).aestronglyMeasurable
    · exact (pow_unit hF (by linarith)).intv
    · exact ((hF.1.pow_const NG).mul (Real.measurable_log.comp hF.1)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t _ N hN => ?_
      rw [Real.norm_eq_abs]
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hN
      exact powlog_bound (hF.2 t).1 (hF.2 t).2 (by linarith)
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun t _ N hN => ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hN
      exact powlog_deriv (hF.2 t).1 (by linarith)
  have := ((hasDerivAt_const NG (1:ℝ)).sub hD).sub ((hasDerivAt_id' NG).mul_const c)
  exact this.congr_deriv (by ring)

lemma pos_part {F G : ℝ → ℝ} (hF : Unit01 F) (hG : Unit01 G)
    (hGF : ∀ x ∈ Ioo (0:ℝ) 1, G x ≤ F x)
    (hnd : 0 < volume {x ∈ Ioo (0 : ℝ) 1 | 0 < G x ∧ F x < 1}) {N : ℝ} (hN : 1 ≤ N) :
    0 < -(∫ z in (0 : ℝ)..1, F z ^ N * Real.log (F z)) - piReg F G N := by
  have hmeas : Measurable fun z => -(F z ^ N * Real.log (F z)) :=
    ((hF.1.pow_const N).mul (Real.measurable_log.comp hF.1)).neg
  have hint : IntervalIntegrable (fun z => -(F z ^ N * Real.log (F z))) volume 0 1 :=
    intv_of_bdd hmeas fun x => by
      rw [abs_neg]
      rcases eq_or_lt_of_le (hF.2 x).1 with h | h
      · rw [← h]; simp
      have := Real.abs_log_mul_self_rpow_lt (F x) N h (hF.2 x).2 (by linarith)
      rw [mul_comm]
      have h2 : 1 / N ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
  have key : piReg F G N < ∫ z in (0 : ℝ)..1, -(F z ^ N * Real.log (F z)) := by
    unfold piReg
    have pt : ∀ x ∈ Ioo (0:ℝ) 1, 0 < F x →
        (1 - F x) * G x * F x ^ (N - 1) ≤ (1 - F x) * F x ^ N ∧
        (F x < 1 → (1 - F x) * F x ^ N < -(F x ^ N * Real.log (F x))) := by
      intro x hx h0
      have hb : F x ^ N = F x * F x ^ (N - 1) := by
        conv_lhs => rw [show N = 1 + (N - 1) by ring]
        rw [Real.rpow_add h0, Real.rpow_one]
      have hpN : 0 < F x ^ N := Real.rpow_pos_of_pos h0 _
      refine ⟨?_, fun h1 => ?_⟩
      · rw [hb]
        have := mul_le_mul_of_nonneg_right (hGF x hx)
          (mul_nonneg (by linarith [(hF.2 x).2] : (0:ℝ) ≤ 1 - F x)
            (Real.rpow_nonneg (hF.2 x).1 (N - 1)))
        nlinarith
      · have := Real.log_lt_sub_one_of_pos h0 h1.ne
        nlinarith
    apply intv_lt (integrand_unit hF hG hN).intv hint
    · intro x hx
      rcases eq_or_lt_of_le (hF.2 x).1 with h | h
      · have hG0 : G x = 0 := le_antisymm (h ▸ hGF x hx) (hG.2 x).1
        rw [hG0, ← h]; simp
      have hl : Real.log (F x) ≤ F x - 1 := Real.log_le_sub_one_of_pos h
      have hpN : 0 ≤ F x ^ N := Real.rpow_nonneg (hF.2 x).1 _
      have := (pt x hx h).1
      nlinarith
    · exact hnd
    · rintro x ⟨hx, h0, h1⟩
      have hF0 : 0 < F x := lt_of_lt_of_le h0 (hGF x hx)
      exact ⟨hx, lt_of_le_of_lt (pt x hx hF0).1 ((pt x hx hF0).2 h1)⟩
  rw [intervalIntegral.integral_neg] at key
  linarith

end SBAHelp

open StrongBuyerAuction.FreeEntry in
theorem solution (μF μG : Measure ℝ)
    (hμF : IsValueLaw μF) (hμG : IsValueLaw μG)
    (c : ℝ) (hc : 0 < c)
    (hGF : FOSD (cdf μG) (cdf μF))
    (hnd : ProfitNondegenerate (cdf μF) (cdf μG))
    (NG : ℝ) (hNG : IsFreeEntry (cdf μF) (cdf μG) c NG) :
    HasDerivAt
      (fun N : ℝ => 1 - (∫ z in (0 : ℝ)..1, (cdf μF z) ^ N) - N * c)
      (-(∫ z in (0 : ℝ)..1, (cdf μF z) ^ NG * Real.log (cdf μF z)) - c) NG ∧
    0 < -(∫ z in (0 : ℝ)..1, (cdf μF z) ^ NG * Real.log (cdf μF z)) -
      piReg (cdf μF) (cdf μG) NG :=
  ⟨SBAHelp.deriv_part (SBAHelp.unit_cdf μF) hNG.2,
   SBAHelp.pos_part (SBAHelp.unit_cdf μF) (SBAHelp.unit_cdf μG) hGF.1 hnd hNG.2⟩
