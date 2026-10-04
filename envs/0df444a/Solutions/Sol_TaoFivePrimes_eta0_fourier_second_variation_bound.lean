-- Prove2me | solution 1 for TaoFivePrimes.eta0_fourier_second_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T01:02:39.729402+00:00
-- url     : https://prove2.me/submissions/26dc132a-e4da-47d0-be09-5870fb390c97

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

set_option autoImplicit false

open MeasureTheory

namespace P7222e51c

lemma ibp2 (k : ℂ) (hk : k ≠ 0) (a b : ℝ) (hab : a ≤ b) (f f1 f2 : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x ∈ Set.Icc a b, HasDerivAt f1 (f2 x) x)
    (hc : ContinuousOn f2 (Set.Icc a b)) :
    ∫ x in a..b, (f x : ℂ) * Complex.exp (k * x) =
      ((f b : ℂ) * Complex.exp (k * b) / k - (f1 b : ℂ) * Complex.exp (k * b) / k ^ 2) -
      ((f a : ℂ) * Complex.exp (k * a) / k - (f1 a : ℂ) * Complex.exp (k * a) / k ^ 2) +
      ∫ x in a..b, (f2 x : ℂ) * Complex.exp (k * x) / k ^ 2 := by
  have hE : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (k * y)) (Complex.exp (k * x) * k) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => k * (y : ℂ)) (k * 1) x :=
      (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul k
    simpa using h1.cexp
  have hcf : ContinuousOn f (Set.Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hcont1 : ContinuousOn (fun x : ℝ => (f x : ℂ) * Complex.exp (k * x)) (Set.Icc a b) := by
    apply ContinuousOn.mul
    · exact Complex.continuous_ofReal.comp_continuousOn hcf
    · exact (Continuous.cexp (continuous_const.mul Complex.continuous_ofReal)).continuousOn
  have hcont2 : ContinuousOn (fun x : ℝ => (f2 x : ℂ) * Complex.exp (k * x) / k ^ 2) (Set.Icc a b) := by
    apply ContinuousOn.div_const
    apply ContinuousOn.mul
    · exact Complex.continuous_ofReal.comp_continuousOn hc
    · exact (Continuous.cexp (continuous_const.mul Complex.continuous_ofReal)).continuousOn
  have hi1 : IntervalIntegrable (fun x : ℝ => (f x : ℂ) * Complex.exp (k * x)) volume a b :=
    (hcont1.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable
  have hi2 : IntervalIntegrable (fun x : ℝ => (f2 x : ℂ) * Complex.exp (k * x) / k ^ 2) volume a b :=
    (hcont2.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => (f x : ℂ) * Complex.exp (k * x) / k - (f1 x : ℂ) * Complex.exp (k * x) / k ^ 2)
    (f' := fun x : ℝ => (f x : ℂ) * Complex.exp (k * x) - (f2 x : ℂ) * Complex.exp (k * x) / k ^ 2)
    (a := a) (b := b) ?_ (hi1.sub hi2)
  · rw [intervalIntegral.integral_sub hi1 hi2] at hFTC
    linear_combination hFTC
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have d1 := ((hf x hx).ofReal_comp.mul (hE x)).div_const k
    have d2 := ((hf1 x hx).ofReal_comp.mul (hE x)).div_const (k ^ 2)
    convert d1.sub d2 using 1
    · funext y
      simp only [Pi.mul_apply, Pi.sub_apply]
    · field_simp
      ring

lemma normE (k : ℂ) (hk : k.re = 0) (x : ℝ) : ‖Complex.exp (k * x)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [hk]

lemma bnd (k : ℂ) (hkre : k.re = 0) (a b : ℝ) (hab : a ≤ b) (f2 : ℝ → ℝ)
    (hc : ContinuousOn f2 (Set.Icc a b)) :
    ‖∫ x in a..b, (f2 x : ℂ) * Complex.exp (k * x) / k ^ 2‖ ≤ (∫ x in a..b, |f2 x|) / ‖k‖ ^ 2 := by
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.norm_integral_le_of_norm_le hab
  · filter_upwards with x hx
    rw [norm_div, norm_mul, normE k hkre x, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_one]
  · exact ((hc.abs.div_const _).mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable

noncomputable def fA (t : ℝ) : ℝ := 4 * (2 * Real.log 2 + Real.log t)
noncomputable def fA1 (t : ℝ) : ℝ := 4 * t⁻¹
noncomputable def fA2 (t : ℝ) : ℝ := 4 * (-(t ^ 2)⁻¹)
noncomputable def fB (t : ℝ) : ℝ := -4 * Real.log t
noncomputable def fB1 (t : ℝ) : ℝ := -4 * t⁻¹
noncomputable def fB2 (t : ℝ) : ℝ := -4 * (-(t ^ 2)⁻¹)

lemma dA {x : ℝ} (hx : 0 < x) : HasDerivAt fA (fA1 x) x := by
  have := ((Real.hasDerivAt_log hx.ne').const_add (2 * Real.log 2)).const_mul 4
  exact this
lemma dA1 {x : ℝ} (hx : 0 < x) : HasDerivAt fA1 (fA2 x) x := by
  have := (hasDerivAt_inv hx.ne').const_mul 4
  exact this
lemma dB {x : ℝ} (hx : 0 < x) : HasDerivAt fB (fB1 x) x := by
  have := (Real.hasDerivAt_log hx.ne').const_mul (-4)
  exact this
lemma dB1 {x : ℝ} (hx : 0 < x) : HasDerivAt fB1 (fB2 x) x := by
  have := (hasDerivAt_inv hx.ne').const_mul (-4)
  exact this

lemma cA2 (a b : ℝ) (ha : 0 < a) : ContinuousOn fA2 (Set.Icc a b) := by
  intro x hx
  have hx0 : x ≠ 0 := (lt_of_lt_of_le ha hx.1).ne'
  unfold fA2
  exact (continuousAt_const.mul ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hx0)).neg).continuousWithinAt
lemma cB2 (a b : ℝ) (ha : 0 < a) : ContinuousOn fB2 (Set.Icc a b) := by
  intro x hx
  have hx0 : x ≠ 0 := (lt_of_lt_of_le ha hx.1).ne'
  unfold fB2
  exact (continuousAt_const.mul ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hx0)).neg).continuousWithinAt

lemma intA : (∫ x in (1/4 : ℝ)..(1/2), |fA2 x|) = 8 := by
  have h1 : (∫ x in (1/4 : ℝ)..(1/2), |fA2 x|) = ∫ x in (1/4 : ℝ)..(1/2), -fA2 x := by
    apply intervalIntegral.integral_congr
    intro x _
    have : fA2 x ≤ 0 := by
      unfold fA2
      have : 0 ≤ (x ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg x)
      linarith
    simp [abs_of_nonpos this]
  rw [h1, intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fA1)]
  · unfold fA1; norm_num
  · intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    exact dA1 (by linarith [hx.1])
  · exact ((cA2 (1/4) (1/2) (by norm_num)).mono (by rw [Set.uIcc_of_le (by norm_num)])).intervalIntegrable

lemma intB : (∫ x in (1/2 : ℝ)..1, |fB2 x|) = 4 := by
  have h1 : (∫ x in (1/2 : ℝ)..1, |fB2 x|) = ∫ x in (1/2 : ℝ)..1, fB2 x := by
    apply intervalIntegral.integral_congr
    intro x _
    have : 0 ≤ fB2 x := by
      unfold fB2
      have : 0 ≤ (x ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg x)
      linarith
    simp [abs_of_nonneg this]
  rw [h1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fB1)]
  · unfold fB1; norm_num
  · intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    exact dB1 (by linarith [hx.1])
  · exact ((cB2 (1/2) 1 (by norm_num)).mono (by rw [Set.uIcc_of_le (by norm_num)])).intervalIntegrable

lemma hl2 : Real.log (1/2) = - Real.log 2 := by rw [one_div, Real.log_inv]
lemma hl4 : Real.log (1/4) = -2 * Real.log 2 := by
  rw [one_div, Real.log_inv, show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

lemma etaA (t : ℝ) (h : t ∈ Set.Icc (1/4 : ℝ) (1/2)) : TaoFivePrimes.eta0 t = fA t := by
  have ht : 0 < t := by linarith [h.1]
  have hu : Real.log t ≤ - Real.log 2 := by
    rw [← hl2]; exact Real.log_le_log ht h.2
  have hd : -2 * Real.log 2 ≤ Real.log t := by
    rw [← hl4]; exact Real.log_le_log (by norm_num) h.1
  unfold TaoFivePrimes.eta0 fA
  rw [if_pos ht, Real.log_mul two_ne_zero ht.ne', abs_of_nonpos (by linarith),
    max_eq_right (by linarith)]
  ring

lemma etaB (t : ℝ) (h : t ∈ Set.Icc (1/2 : ℝ) 1) : TaoFivePrimes.eta0 t = fB t := by
  have ht : 0 < t := by linarith [h.1]
  have hu : Real.log t ≤ 0 := Real.log_nonpos ht.le h.2
  have hd : - Real.log 2 ≤ Real.log t := by
    rw [← hl2]; exact Real.log_le_log (by norm_num) h.1
  unfold TaoFivePrimes.eta0 fB
  rw [if_pos ht, Real.log_mul two_ne_zero ht.ne', abs_of_nonneg (by linarith),
    max_eq_right (by linarith)]
  ring

lemma etaOut (t : ℝ) (h : t ∉ Set.Icc (1/4 : ℝ) 1) : TaoFivePrimes.eta0 t = 0 := by
  unfold TaoFivePrimes.eta0
  split_ifs with ht
  · have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [Real.log_mul two_ne_zero ht.ne']
    rcases not_and_or.mp h with h1 | h1
    · push_neg at h1
      have : Real.log t < -2 * Real.log 2 := by rw [← hl4]; exact Real.log_lt_log ht h1
      rw [abs_of_neg (by linarith)]
      simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      exact max_eq_left (by linarith)
    · push_neg at h1
      have : 0 < Real.log t := Real.log_pos h1
      rw [abs_of_pos (by linarith)]
      simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      exact max_eq_left (by linarith)
  · rfl

lemma contPiece (k : ℂ) (a b : ℝ) (f : ℝ → ℝ) (f1 : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f1 x) x) :
    ContinuousOn (fun x : ℝ => (f x : ℂ) * Complex.exp (k * x)) (Set.Icc a b) := by
  have hcf : ContinuousOn f (Set.Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  apply ContinuousOn.mul
  · exact Complex.continuous_ofReal.comp_continuousOn hcf
  · exact (Continuous.cexp (continuous_const.mul Complex.continuous_ofReal)).continuousOn

lemma main (k : ℂ) (hk : k ≠ 0) (hkre : k.re = 0) :
    ‖∫ t : ℝ, (TaoFivePrimes.eta0 t : ℂ) * Complex.exp (k * t)‖ ≤ 48 / ‖k‖ ^ 2 := by
  set g : ℝ → ℂ := fun t => (TaoFivePrimes.eta0 t : ℂ) * Complex.exp (k * t) with hg
  have hind : g = Set.indicator (Set.Icc (1/4 : ℝ) 1) g := by
    funext t
    by_cases ht : t ∈ Set.Icc (1/4 : ℝ) 1
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]
      simp [hg, etaOut t ht]
  have hAcont : ∀ x ∈ Set.Icc (1/4 : ℝ) (1/2), HasDerivAt fA (fA1 x) x :=
    fun x hx => dA (by linarith [hx.1])
  have hA1 : ∀ x ∈ Set.Icc (1/4 : ℝ) (1/2), HasDerivAt fA1 (fA2 x) x :=
    fun x hx => dA1 (by linarith [hx.1])
  have hBcont : ∀ x ∈ Set.Icc (1/2 : ℝ) 1, HasDerivAt fB (fB1 x) x :=
    fun x hx => dB (by linarith [hx.1])
  have hB1 : ∀ x ∈ Set.Icc (1/2 : ℝ) 1, HasDerivAt fB1 (fB2 x) x :=
    fun x hx => dB1 (by linarith [hx.1])
  have eqA : Set.EqOn g (fun x : ℝ => (fA x : ℂ) * Complex.exp (k * x)) (Set.Icc (1/4 : ℝ) (1/2)) := by
    intro x hx; simp [hg, etaA x hx]
  have eqB : Set.EqOn g (fun x : ℝ => (fB x : ℂ) * Complex.exp (k * x)) (Set.Icc (1/2 : ℝ) 1) := by
    intro x hx; simp [hg, etaB x hx]
  have iA : IntervalIntegrable g volume (1/4 : ℝ) (1/2) :=
    (((contPiece k _ _ fA fA1 hAcont).congr eqA).mono
      (by rw [Set.uIcc_of_le (by norm_num)])).intervalIntegrable
  have iB : IntervalIntegrable g volume (1/2 : ℝ) 1 :=
    (((contPiece k _ _ fB fB1 hBcont).congr eqB).mono
      (by rw [Set.uIcc_of_le (by norm_num)])).intervalIntegrable
  have hsplit : ∫ t : ℝ, g t = (∫ x in (1/4 : ℝ)..(1/2), g x) + ∫ x in (1/2 : ℝ)..1, g x := by
    rw [intervalIntegral.integral_add_adjacent_intervals iA iB, hind,
      integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by norm_num)]
    congr 1
  have pA : (∫ x in (1/4 : ℝ)..(1/2), g x) = ∫ x in (1/4 : ℝ)..(1/2), (fA x : ℂ) * Complex.exp (k * x) :=
    intervalIntegral.integral_congr (by rw [Set.uIcc_of_le (by norm_num)]; exact eqA)
  have pB : (∫ x in (1/2 : ℝ)..1, g x) = ∫ x in (1/2 : ℝ)..1, (fB x : ℂ) * Complex.exp (k * x) :=
    intervalIntegral.integral_congr (by rw [Set.uIcc_of_le (by norm_num)]; exact eqB)
  rw [hsplit, pA, pB, ibp2 k hk _ _ (by norm_num) fA fA1 fA2 hAcont hA1 (cA2 _ _ (by norm_num)),
    ibp2 k hk _ _ (by norm_num) fB fB1 fB2 hBcont hB1 (cB2 _ _ (by norm_num))]
  have v1 : fA (1/4) = 0 := by unfold fA; rw [hl4]; ring
  have v2 : fA (1/2) = 4 * Real.log 2 := by unfold fA; rw [hl2]; ring
  have v3 : fB (1/2) = 4 * Real.log 2 := by unfold fB; rw [hl2]; ring
  have v4 : fB 1 = 0 := by unfold fB; simp
  have w1 : fA1 (1/4) = 16 := by unfold fA1; norm_num
  have w2 : fA1 (1/2) = 8 := by unfold fA1; norm_num
  have w3 : fB1 (1/2) = -8 := by unfold fB1; norm_num
  have w4 : fB1 1 = -4 := by unfold fB1; norm_num
  set IA := ∫ x in (1/4 : ℝ)..(1/2), (fA2 x : ℂ) * Complex.exp (k * x) / k ^ 2 with hIA
  set IB := ∫ x in (1/2 : ℝ)..1, (fB2 x : ℂ) * Complex.exp (k * x) / k ^ 2 with hIB
  set E1 := Complex.exp (k * ((1/4 : ℝ) : ℂ))
  set E2 := Complex.exp (k * ((1/2 : ℝ) : ℂ))
  set E3 := Complex.exp (k * ((1 : ℝ) : ℂ))
  rw [v1, v2, v3, v4, w1, w2, w3, w4]
  have hrw : ((((4 * Real.log 2 : ℝ) : ℂ) * E2 / k - ((8 : ℝ) : ℂ) * E2 / k ^ 2) -
        (((0 : ℝ) : ℂ) * E1 / k - ((16 : ℝ) : ℂ) * E1 / k ^ 2) + IA) +
      ((((0 : ℝ) : ℂ) * E3 / k - ((-4 : ℝ) : ℂ) * E3 / k ^ 2) -
        (((4 * Real.log 2 : ℝ) : ℂ) * E2 / k - ((-8 : ℝ) : ℂ) * E2 / k ^ 2) + IB) =
      (16 * E1 / k ^ 2 - 16 * E2 / k ^ 2) + 4 * E3 / k ^ 2 + IA + IB := by
    push_cast; ring
  rw [hrw]
  have hn : ∀ (c : ℝ) (x : ℝ), 0 ≤ c → ‖(c : ℂ) * Complex.exp (k * (x : ℂ)) / k ^ 2‖ = c / ‖k‖ ^ 2 := by
    intro c x hc
    rw [norm_div, norm_mul, normE k hkre x, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc, mul_one]
  have n1 : ‖16 * E1 / k ^ 2‖ = 16 / ‖k‖ ^ 2 := by
    have := hn 16 (1/4) (by norm_num); rwa [Complex.ofReal_ofNat] at this
  have n2 : ‖16 * E2 / k ^ 2‖ = 16 / ‖k‖ ^ 2 := by
    have := hn 16 (1/2) (by norm_num); rwa [Complex.ofReal_ofNat] at this
  have n3 : ‖4 * E3 / k ^ 2‖ = 4 / ‖k‖ ^ 2 := by
    have := hn 4 1 (by norm_num); rwa [Complex.ofReal_ofNat] at this
  have bA := bnd k hkre (1/4) (1/2) (by norm_num) fA2 (cA2 _ _ (by norm_num))
  have bB := bnd k hkre (1/2) 1 (by norm_num) fB2 (cB2 _ _ (by norm_num))
  rw [intA] at bA
  rw [intB] at bB
  have hk2 : 0 < ‖k‖ ^ 2 := by positivity
  calc ‖(16 * E1 / k ^ 2 - 16 * E2 / k ^ 2) + 4 * E3 / k ^ 2 + IA + IB‖
      ≤ ‖16 * E1 / k ^ 2‖ + ‖16 * E2 / k ^ 2‖ + ‖4 * E3 / k ^ 2‖ + ‖IA‖ + ‖IB‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_sub_le _ _
    _ ≤ 16 / ‖k‖ ^ 2 + 16 / ‖k‖ ^ 2 + 4 / ‖k‖ ^ 2 + 8 / ‖k‖ ^ 2 + 4 / ‖k‖ ^ 2 := by
        rw [n1, n2, n3]; linarith
    _ = 48 / ‖k‖ ^ 2 := by ring

end P7222e51c

open MeasureTheory in
theorem solution (alpha : ℝ) (halpha : alpha ≠ 0) :
    ‖∫ t : ℝ, (TaoFivePrimes.eta0 t : ℂ) * TaoFivePrimes.expCircle (alpha * t)‖ ≤
      48 / (2 * Real.pi * alpha) ^ 2 := by
  set k : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (alpha : ℂ) with hk
  have hk0 : k ≠ 0 := by
    simp [hk, Real.pi_ne_zero, halpha, Complex.I_ne_zero]
  have hkre : k.re = 0 := by simp [hk]
  have hnk : ‖k‖ ^ 2 = (2 * Real.pi * alpha) ^ 2 := by
    rw [hk, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    simp only [Complex.norm_ofNat, mul_one, mul_pow, sq_abs]
  have hE : ∀ t : ℝ, TaoFivePrimes.expCircle (alpha * t) = Complex.exp (k * t) := by
    intro t
    unfold TaoFivePrimes.expCircle
    rw [hk]; push_cast; ring_nf
  simp_rw [hE]
  rw [← hnk]
  exact P7222e51c.main k hk0 hkre
