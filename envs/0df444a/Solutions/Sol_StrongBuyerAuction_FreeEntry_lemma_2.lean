-- Prove2me | solution 1 for StrongBuyerAuction.FreeEntry.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:59:47.268307+00:00
-- url     : https://prove2.me/submissions/89e8e294-5a1d-4184-ba67-a82f15392d92

import Mathlib
import Definitions.Def_StrongBuyerAuction_FreeEntry_Model
import Theorems.Thm_StrongBuyerAuction_FreeEntry_lemma_1_dominance

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

open StrongBuyerAuction.FreeEntry in
theorem solution (μF μG μG' : Measure ℝ)
    (hμF : IsValueLaw μF) (hμG : IsValueLaw μG) (hμG' : IsValueLaw μG')
    (c : ℝ) (hc : 0 < c)
    (hGF : FOSD (cdf μG) (cdf μF))
    (hG'G : FOSD (cdf μG') (cdf μG))
    (hguard : StrictWhereOpen (cdf μF) (cdf μG') (cdf μG))
    (NG NG' : ℝ)
    (hNG : IsFreeEntry (cdf μF) (cdf μG) c NG)
    (hNG' : IsFreeEntry (cdf μF) (cdf μG') c NG') :
    NG' < NG := by
  by_contra h
  push Not at h
  -- Lemma 1 (dominance): π(N_{G'} | G') < π(N_{G'} | G)
  have h1 := lemma_1_dominance μF μG μG' hμF hμG hμG' c hc hGF hG'G hguard NG' hNG'.2
  -- Lemma 1 (entry, weak form): π(N_{G'} | G) ≤ π(N_G | G) since N_G ≤ N_{G'}
  have h2 := SBAHelp.piReg_anti (SBAHelp.unit_cdf μF) (SBAHelp.unit_cdf μG) hNG.2 h
  linarith [hNG.1, hNG'.1]
