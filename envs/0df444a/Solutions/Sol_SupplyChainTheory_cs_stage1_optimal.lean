-- Prove2me | solution 1 for SupplyChainTheory.cs_stage1_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T16:44:38.857269+00:00
-- url     : https://prove2.me/submissions/29c57825-be67-4799-859a-631e1ceb28bb

import Mathlib
import Definitions.Def_SupplyChainTheory_multiechelon

set_option autoImplicit false

open MeasureTheory in
lemma d77f_int_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hid : Integrable (fun x : ℝ => x) μ) (y : ℝ) :
    Integrable (fun x : ℝ => max (x - y) 0) μ :=
  (hid.sub (integrable_const y)).pos_part

open MeasureTheory ProbabilityTheory in
lemma d77f_loss_sub (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hid : Integrable (fun x : ℝ => x) μ) (a z : ℝ) :
    ∫ x, max (x - a) 0 ∂μ + (a - z) * (1 - cdf μ a) ≤ ∫ x, max (x - z) 0 ∂μ := by
  have hP : μ.real (Set.Ioi a) = 1 - cdf μ a := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real]
  have hz := d77f_int_pos μ hid z
  have ha := d77f_int_pos μ hid a
  have hind : Integrable (fun x : ℝ => (a - z) * (Set.Ioi a).indicator (fun _ => (1:ℝ)) x) μ :=
    ((integrable_const (1:ℝ)).indicator measurableSet_Ioi).const_mul _
  have hle : ∫ x, max (x - a) 0 ∂μ
      + ∫ x, (a - z) * (Set.Ioi a).indicator (fun _ => (1:ℝ)) x ∂μ
      ≤ ∫ x, max (x - z) 0 ∂μ := by
    rw [← integral_add ha hind]
    apply integral_mono (ha.add hind) hz
    intro x
    show max (x - a) 0 + (a - z) * (Set.Ioi a).indicator (fun _ => (1:ℝ)) x ≤ max (x - z) 0
    simp only [Set.indicator, Set.mem_Ioi]
    split_ifs with h
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ x - a)]
      have := le_max_left (x - z) 0
      linarith
    · rw [max_eq_right (by linarith : x - a ≤ 0)]
      have := le_max_right (x - z) 0
      linarith
  have hint : ∫ x, (a - z) * (Set.Ioi a).indicator (fun _ => (1:ℝ)) x ∂μ
      = (a - z) * (1 - cdf μ a) := by
    rw [integral_const_mul, integral_indicator_const _ measurableSet_Ioi, hP, smul_eq_mul, mul_one]
  rw [hint] at hle
  exact hle

open MeasureTheory SupplyChainTheory in
lemma d77f_G_eq (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ)
    [IsProbabilityMeasure (D 1)] (hid : Integrable (fun x : ℝ => x) (D 1)) (y : ℝ) :
    csG N h p D S 1 y = h 1 * (y - ∫ x, x ∂(D 1))
      + (p + localHolding N h 1) * ∫ x, max (x - y) 0 ∂(D 1) := by
  unfold csG csHat
  have e : (fun d => h 1 * (y - d) + csBar N h p D S (1 - 1) (y - d))
      = fun d => (h 1 * y - h 1 * d) + (p + localHolding N h 1) * max (d - y) 0 := by
    funext d
    show h 1 * (y - d) + (p + localHolding N h 1) * max (-(y - d)) 0 = _
    rw [neg_sub]
    ring
  have i1 : Integrable (fun d : ℝ => h 1 * y - h 1 * d) (D 1) :=
    (integrable_const _).sub (hid.const_mul _)
  have i2 : Integrable (fun d : ℝ => (p + localHolding N h 1) * max (d - y) 0) (D 1) :=
    (d77f_int_pos _ hid y).const_mul _
  have i3 : Integrable (fun d : ℝ => h 1 * d) (D 1) := hid.const_mul _
  rw [e, integral_add i1 i2, integral_sub (integrable_const _) i3, integral_const,
    integral_const_mul, integral_const_mul, probReal_univ, one_smul]
  ring

lemma d77f_hasDerivAt_of_subgrad (g q : ℝ → ℝ) (y : ℝ)
    (hsub : ∀ a z, q a * (z - a) ≤ g z - g a) (hq : ContinuousAt q y) :
    HasDerivAt g (q y) y := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hev : ∀ᶠ z in nhds y, |q z - q y| < c := by
    have hball := hq (Metric.ball_mem_nhds (q y) hc)
    filter_upwards [hball] with z hz
    have hz' : dist (q z) (q y) < c := hz
    rwa [Real.dist_eq] at hz'
  filter_upwards [hev] with z hz
  have h1 := hsub y z
  have h2 := hsub z y
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul]
  rw [abs_le]
  have h3 : (q z - q y) * (z - y) ≤ |q z - q y| * |z - y| := by
    rw [← abs_mul]; exact le_abs_self _
  have h4 : |q z - q y| * |z - y| ≤ c * |z - y| :=
    mul_le_mul_of_nonneg_right hz.le (abs_nonneg _)
  have h5 : 0 ≤ c * |z - y| := mul_nonneg hc.le (abs_nonneg _)
  constructor
  · nlinarith
  · nlinarith

open MeasureTheory ProbabilityTheory in
lemma d77f_cdf_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    Continuous (cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro a
  have hmono : Monotone (cdf μ) := monotone_cdf _
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
  have hr : Function.rightLim (cdf μ) a = cdf μ a :=
    ((cdf μ).right_continuous a).rightLim_eq
  have hl : Function.leftLim (cdf μ) a = cdf μ a := by
    have h1 := (cdf μ).measure_singleton a
    rw [measure_cdf] at h1
    have h0 : μ {a} = 0 := measure_singleton a
    rw [h0] at h1
    have h2 := hmono.leftLim_le (le_refl a)
    have h3 := ENNReal.ofReal_eq_zero.1 h1.symm
    linarith
  rw [hl, hr]

open MeasureTheory ProbabilityTheory SupplyChainTheory in
lemma d77f_localHolding_split (N : ℕ) (h : ℕ → ℝ) (hN : 1 ≤ N) :
    localHolding N h 1 = h 1 + localHolding N h 2 := by
  unfold localHolding
  have e : Finset.Icc 2 N = Finset.Ioc 1 N := Finset.Icc_add_one_left_eq_Ioc 1 N
  rw [Finset.Icc_eq_cons_Ioc hN, Finset.sum_cons, e]

open MeasureTheory ProbabilityTheory SupplyChainTheory in
theorem solution (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → MeasureTheory.Measure ℝ)
    (S : ℕ → ℝ) (hN : 1 ≤ N) [MeasureTheory.IsProbabilityMeasure (D 1)]
    [MeasureTheory.NullSingletonClass (D 1)]
    (hD : MeasureTheory.Integrable (fun x => x) (D 1)) (hh : 0 < h 1) (hp : 0 < p)
    (hmin : ∀ y, csG N h p D S 1 (S 1) ≤ csG N h p D S 1 y) :
    ProbabilityTheory.cdf (D 1) (S 1)
      = (p + localHolding N h 2) / (h 1 + p + localHolding N h 2) := by
  have hsplit := d77f_localHolding_split N h hN
  set c := p + localHolding N h 1 with hc
  set E := ∫ x, x ∂(D 1) with hE
  have hG : ∀ y, csG N h p D S 1 y = h 1 * (y - E) + c * ∫ x, max (x - y) 0 ∂(D 1) :=
    fun y => d77f_G_eq N h p D S hD y
  rcases lt_or_ge c 0 with hneg | hnn
  · exfalso
    have h1 := hmin (S 1 - 1)
    rw [hG, hG] at h1
    have hmono : ∫ x, max (x - S 1) 0 ∂(D 1) ≤ ∫ x, max (x - (S 1 - 1)) 0 ∂(D 1) := by
      have := d77f_loss_sub (D 1) hD (S 1) (S 1 - 1)
      have hF1 : cdf (D 1) (S 1) ≤ 1 := cdf_le_one _ _
      nlinarith
    have := mul_le_mul_of_nonpos_left hmono hneg.le
    nlinarith
  · set q : ℝ → ℝ := fun a => h 1 + c * (cdf (D 1) a - 1) with hq
    have hsub : ∀ a z, q a * (z - a) ≤ csG N h p D S 1 z - csG N h p D S 1 a := by
      intro a z
      rw [hG, hG]
      have := mul_le_mul_of_nonneg_left (d77f_loss_sub (D 1) hD a z) hnn
      simp only [hq]
      nlinarith
    have hcont : Continuous q :=
      continuous_const.add (continuous_const.mul ((d77f_cdf_cont (D 1)).sub continuous_const))
    have hderiv := d77f_hasDerivAt_of_subgrad _ q (S 1) hsub hcont.continuousAt
    have h0 := IsLocalMin.hasDerivAt_eq_zero (Filter.Eventually.of_forall hmin) hderiv
    simp only [hq] at h0
    have hcpos : c ≠ 0 := by
      intro hc0
      rw [hc0] at h0
      linarith
    have hden : h 1 + p + localHolding N h 2 = c := by rw [hc, hsplit]; ring
    rw [hden, eq_div_iff hcpos]
    rw [hc, hsplit] at h0 ⊢
    linarith
