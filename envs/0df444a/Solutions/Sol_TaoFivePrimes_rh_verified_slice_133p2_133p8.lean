-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_slice_133p2_133p8
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T23:33:35.675312+00:00
-- url     : https://prove2.me/submissions/f4e0996f-6a09-4f2a-8ac7-d155eda65c8b

/- Submission file for Prove2Me theorem
TaoFivePrimes.rh_verified_slice_133p2_133p8 (f129523d, Open).
Submitted with the user's explicit per-item approval (Oct 31, 2026).

Structure: platform imports supply the Proved derivative bound and the
Proved 133.2-133.8 imaginary certificate (bound 11, same centre-132
polynomial). The slice assembly is proved inline, exactly as in the
locally verified twin file next/Slice133Full.lean, where both platform
inputs appear as clearly-labeled axiom stubs with the same names and
statements. On the platform the stubs are these imports, so no extra
axiom remains. This file itself has NOT been compiled in the platform
environment; its import paths follow the proved 134.4-135 submission
(ef827ddc, ACCEPTED), which used the same derivative-bound import. -/
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh132_xi_polynomial_derivative_bound
import Theorems.Thm_TaoFivePrimes_rh133p2to133p8_imaginary_certificate
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000


open Complex Finset
open Finset Polynomial
open scoped unitInterval
set_option autoImplicit false

section Slice133Assembly

open Complex Metric Set Finset
open HurwitzZeta MeasureTheory
open scoped ComplexConjugate

/- The derivative bound and the 133 imaginary certificate are supplied
by the platform imports above (Proved theorems fdbbf536 and
b895a78f); they are cited below by their platform names.
The xi approximation is not used (see the local verification file). -/


namespace Slice133

/-- Bridge lemma: the N=60 polynomial in the derivative bound equals the
N=40 polynomial in the certificate, at the same center 132. Terms with
index ≥ 40 vanish because the coefficient list has length 40, so
`getD` returns the default 0 there. -/
lemma poly60_eq_poly40 (s : ℂ) :
    TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
        (10^14) 60 132 s =
    TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
        (10^14) 40 132 s := by
  have hzero : ∀ i : ℕ,
      ((TaoFivePrimes_RH132RoundedCoefficients14.getD (40 + i) 0:ℝ)/((10^14:ℕ):ℝ):ℂ) *
        (-Complex.I*(s - RH1000Analytic.CertifiedLocalXi.center 132))^(40 + i) = 0 := by
    intro i
    have hlen : TaoFivePrimes_RH132RoundedCoefficients14.length = 40 := rfl
    have hcoeff : TaoFivePrimes_RH132RoundedCoefficients14.getD (40 + i) 0 = 0 := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none_iff.mpr
          (show TaoFivePrimes_RH132RoundedCoefficients14.length ≤ 40 + i by omega)]
      rfl
    rw [hcoeff]
    simp
  unfold TaoFivePrimes_RHLocalRationalPolynomial
  rw [show (60:ℕ) = 40 + 20 from rfl, Finset.sum_range_add,
    Finset.sum_eq_zero (s := Finset.range 20) (fun i _ => hzero i), add_zero]

/-- The local xi function is entire (Mathlib: `differentiable_completedZeta₀`). -/
lemma xi_entire : Differentiable ℂ RH1000Analytic.CertifiedLocalXi.xi := by
  unfold RH1000Analytic.CertifiedLocalXi.xi
  have hΛ := differentiable_completedZeta₀
  fun_prop

/-- The N=60 polynomial is entire. -/
lemma poly_differentiable : Differentiable ℂ
    (fun w => TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
      (10^14) 60 132 w) := by
  unfold TaoFivePrimes_RHLocalRationalPolynomial
  fun_prop

/-- The error function `E(w) = 10^43 * xi(w) - P60(w)`. -/
noncomputable def E (w : ℂ) : ℂ :=
  (10^43:ℂ)*RH1000Analytic.CertifiedLocalXi.xi w -
    TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
      (10^14) 60 132 w

lemma E_differentiable : Differentiable ℂ E :=
  (xi_entire.const_mul _).sub poly_differentiable

/-- Center arithmetic: `center y - center 132 = (y - 132) * I`. -/
lemma center_sub_center (y : ℝ) :
    RH1000Analytic.CertifiedLocalXi.center y -
      RH1000Analytic.CertifiedLocalXi.center 132 =
    ((y - 132:ℝ):ℂ) * Complex.I := by
  apply Complex.ext <;> simp [RH1000Analytic.CertifiedLocalXi.center] <;> ring

/-- Distance from a point to its critical-line projection. -/
lemma proj_dist (z : ℂ) :
    ‖z - RH1000Analytic.CertifiedLocalXi.center z.im‖ = |z.re - 1/2| := by
  have he : z - RH1000Analytic.CertifiedLocalXi.center z.im =
      ((z.re - 1/2:ℝ):ℂ) := by
    apply Complex.ext <;> simp [RH1000Analytic.CertifiedLocalXi.center]
  rw [he, Complex.norm_real, Real.norm_eq_abs]

/-- Every point of the 133.2-133.8 rectangle lies in the derivative ball:
its squared distance to center 132 is at most 1/4 + 81/25 = 349/100 < (61/20)^2. -/
lemma z_in_ball (z : ℂ) (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1)
    (ha : (666/5:ℝ) ≤ z.im) (hb : z.im ≤ (669/5:ℝ)) :
    ‖z - RH1000Analytic.CertifiedLocalXi.center 132‖ ≤ 61/20 := by
  have hsq : ‖z - RH1000Analytic.CertifiedLocalXi.center 132‖^2 =
      (z.re - 1/2)^2 + (z.im - 132)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [RH1000Analytic.CertifiedLocalXi.center]
    ring
  have hbound : (z.re - 1/2)^2 + (z.im - 132)^2 ≤ (61/20)^2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (z.re - 1/2) + 1/2 by linarith)
      (show (0:ℝ) ≤ 1/2 - (z.re - 1/2) by linarith),
      mul_nonneg (show (0:ℝ) ≤ 9/5 - (z.im - 132) by linarith)
      (show (0:ℝ) ≤ (z.im - 132) + 6/5 by linarith)]
  have hnorm : ‖z - RH1000Analytic.CertifiedLocalXi.center 132‖ =
      Real.sqrt ((z.re - 1/2)^2 + (z.im - 132)^2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), hsq]
  rw [hnorm]
  calc Real.sqrt ((z.re - 1/2)^2 + (z.im - 132)^2)
      ≤ Real.sqrt ((61/20)^2) := Real.sqrt_le_sqrt hbound
    _ = 61/20 := Real.sqrt_sq (by norm_num)

/-- The critical-line projection also lies in the derivative ball. -/
lemma proj_in_ball (z : ℂ) (ha : (666/5:ℝ) ≤ z.im) (hb : z.im ≤ (669/5:ℝ)) :
    ‖RH1000Analytic.CertifiedLocalXi.center z.im -
      RH1000Analytic.CertifiedLocalXi.center 132‖ ≤ 61/20 := by
  rw [center_sub_center, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-! ### Conjugation of the completed zeta function (adapted from the
accepted 105-106 proof, which proved these lemmas for the same
`hurwitzEvenFEPair 0` pair that the platform analytic model defines
as `RH1000Analytic.ZetaSix.P`). -/

end Slice133

namespace RH1000Analytic.ZetaSix

lemma f_modif_of_one_lt {t : ℝ} (ht : 1 < t) :
    P.f_modif t = ((evenKernel 0 t : ℝ) : ℂ) - 1 := by
  simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, ht, not_lt.2 ht.le,
    Set.indicator_of_notMem]

lemma f_modif_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    P.f_modif t = ((evenKernel 0 t : ℝ) : ℂ) - ((t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
  simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, h0, h1, not_lt.2 h1.le]
  norm_num

lemma f_modif_one : P.f_modif 1 = 0 := by
  simp [P, WeakFEPair.f_modif]

end RH1000Analytic.ZetaSix

namespace Slice133

lemma conj_kernel {t : ℝ} (ht : 0 < t) :
    conj (RH1000Analytic.ZetaSix.P.f_modif t) =
      RH1000Analytic.ZetaSix.P.f_modif t := by
  rcases lt_trichotomy t 1 with h | rfl | h
  · rw [RH1000Analytic.ZetaSix.f_modif_of_lt_one ht h]
    simp
  · rw [RH1000Analytic.ZetaSix.f_modif_one]
    simp
  · rw [RH1000Analytic.ZetaSix.f_modif_of_one_lt h]
    simp

lemma completedZeta_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  change mellin RH1000Analytic.ZetaSix.P.f_modif (conj s / 2) / 2 =
    conj (mellin RH1000Analytic.ZetaSix.P.f_modif (s / 2) / 2)
  rw [map_div₀, map_ofNat]
  congr 1
  rw [mellin, mellin, ← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := ht
  have htarg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht0.le]
    exact ne_of_lt Real.pi_pos
  have he : conj s / 2 - 1 = conj (s / 2 - 1) := by
    simp only [map_sub, map_div₀, map_one, map_ofNat]
  dsimp only
  rw [he, Complex.cpow_conj _ _ htarg]
  simp only [smul_eq_mul, map_mul, conj_ofReal, conj_kernel ht0]

/-- xi is real on the critical line: `conj (center y) = 1 - center y`,
conjugation of Λ₀, and the functional equation Λ₀(1 - s) = Λ₀(s). -/
lemma xi_critical_real (y : ℝ) :
    (RH1000Analytic.CertifiedLocalXi.xi
      (RH1000Analytic.CertifiedLocalXi.center y)).im = 0 := by
  have hc : conj (RH1000Analytic.CertifiedLocalXi.center y) =
      1 - RH1000Analytic.CertifiedLocalXi.center y := by
    apply Complex.ext <;> simp [RH1000Analytic.CertifiedLocalXi.center] <;> ring
  have he := completedZeta_conj (RH1000Analytic.CertifiedLocalXi.center y)
  rw [hc, completedRiemannZeta₀_one_sub] at he
  have hi := congrArg Complex.im he
  simp only [conj_im] at hi
  have hΛ : (completedRiemannZeta₀
      (RH1000Analytic.CertifiedLocalXi.center y)).im = 0 := by linarith
  have hf : (RH1000Analytic.CertifiedLocalXi.center y *
      (RH1000Analytic.CertifiedLocalXi.center y - 1) / 2).im = 0 := by
    norm_num [RH1000Analytic.CertifiedLocalXi.center, Complex.mul_im]
    ring
  unfold RH1000Analytic.CertifiedLocalXi.xi
  simp [Complex.mul_im, hf, hΛ]

/-- The polynomial is real on the critical line: the rotated variable
`-I * (center y - center 132)` equals the real number `y - 132`, so
every term is a real coefficient times a real power. -/
lemma poly60_critical_real (y : ℝ) :
    (TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
      (10^14) 60 132 (RH1000Analytic.CertifiedLocalXi.center y)).im = 0 := by
  have hrot : -Complex.I * (RH1000Analytic.CertifiedLocalXi.center y -
      RH1000Analytic.CertifiedLocalXi.center 132) = ((y - 132:ℝ):ℂ) := by
    apply Complex.ext <;> simp [RH1000Analytic.CertifiedLocalXi.center] <;> ring
  have he : TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
      (10^14) 60 132 (RH1000Analytic.CertifiedLocalXi.center y) =
      ((∑ n ∈ Finset.range 60,
        ((TaoFivePrimes_RH132RoundedCoefficients14.getD n 0:ℝ)/((10^14:ℕ):ℝ)) *
          (y - 132)^n : ℝ):ℂ) := by
    simp only [TaoFivePrimes_RHLocalRationalPolynomial, hrot, Complex.ofReal_sum,
      Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_intCast, Complex.ofReal_natCast]
  rw [he]
  exact Complex.ofReal_im _

/-- The error function is imaginary-zero on the critical line. -/
lemma E_critical_real (y : ℝ) :
    (E (RH1000Analytic.CertifiedLocalXi.center y)).im = 0 := by
  unfold E
  rw [Complex.sub_im]
  have hxi : ((10^43:ℂ) * RH1000Analytic.CertifiedLocalXi.xi
      (RH1000Analytic.CertifiedLocalXi.center y)).im = 0 := by
    rw [Complex.mul_im, xi_critical_real, mul_zero, zero_add]
    have h10 : (10^43:ℂ).im = 0 := by
      rw [show (10^43:ℂ) = ((10^43:ℝ):ℂ) by norm_num]
      exact Complex.ofReal_im _
    rw [h10, zero_mul]
  rw [hxi, poly60_critical_real, sub_zero]

/-- Lipschitz bound for the imaginary part of the error, directly from
the Proved derivative bound via the mean value theorem on the closed
ball of radius 61/20 about center 132 (no Cauchy step, no xi
approximation). The segment from `z` to its critical-line projection
stays in the ball by convexity. -/
lemma imag_error_bound (z : ℂ) (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1)
    (ha : (666/5:ℝ) ≤ z.im) (hb : z.im ≤ (669/5:ℝ)) :
    |(E z).im| ≤ (27/50) * |z.re - 1/2| := by
  have hEp : (E (RH1000Analytic.CertifiedLocalXi.center z.im)).im = 0 :=
    E_critical_real z.im
  have hball_z : z ∈ Metric.closedBall
      (RH1000Analytic.CertifiedLocalXi.center 132) (61/20:ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact z_in_ball z h0 h1 ha hb
  have hball_p : RH1000Analytic.CertifiedLocalXi.center z.im ∈ Metric.closedBall
      (RH1000Analytic.CertifiedLocalXi.center 132) (61/20:ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact proj_in_ball z ha hb
  have hdiff : ∀ w ∈ Metric.closedBall
      (RH1000Analytic.CertifiedLocalXi.center 132) (61/20:ℝ),
      DifferentiableAt ℂ E w :=
    fun w _ => E_differentiable.differentiableAt
  have hbound : ∀ w ∈ Metric.closedBall
      (RH1000Analytic.CertifiedLocalXi.center 132) (61/20:ℝ),
      ‖deriv E w‖ ≤ 27/50 := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    show ‖deriv (fun w : ℂ => (10^43:ℂ)*RH1000Analytic.CertifiedLocalXi.xi w -
      TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
        (10^14) 60 132 w) w‖ ≤ 27/50
    exact TaoFivePrimes.rh132_xi_polynomial_derivative_bound w hw
  have hlip := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_closedBall _ _) hball_p hball_z
  have hdist : ‖z - RH1000Analytic.CertifiedLocalXi.center z.im‖ = |z.re - 1/2| :=
    proj_dist z
  have him : (E z).im = (E z - E (RH1000Analytic.CertifiedLocalXi.center z.im)).im := by
    rw [Complex.sub_im, hEp, sub_zero]
  rw [him]
  calc |(E z - E (RH1000Analytic.CertifiedLocalXi.center z.im)).im|
      ≤ ‖E z - E (RH1000Analytic.CertifiedLocalXi.center z.im)‖ :=
        Complex.abs_im_le_norm _
    _ ≤ (27/50) * ‖z - RH1000Analytic.CertifiedLocalXi.center z.im‖ := hlip
    _ = (27/50) * |z.re - 1/2| := by rw [hdist]

/-- xi has no zero off the critical line in the rectangle: the
certificate gives `|Im P40| ≥ 11|σ - 1/2|` while the error bound gives
`|Im E| ≤ (27/50)|σ - 1/2|`, and `E = -P40` at a zero of xi. -/
lemma xi_nonzero_off_line (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (666/5:ℝ) ≤ s.im) (hb : s.im ≤ (669/5:ℝ)) (hneq : s.re ≠ 1/2) :
    RH1000Analytic.CertifiedLocalXi.xi s ≠ 0 := by
  intro hzero
  have hcert := TaoFivePrimes.rh133p2to133p8_imaginary_certificate s h0 h1 ha hb
  rw [show (264/2:ℝ) = 132 by norm_num] at hcert
  have hEim : |(E s).im| =
      |(TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
        (10^14) 40 132 s).im| := by
    have h1 : E s = - TaoFivePrimes_RHLocalRationalPolynomial
        TaoFivePrimes_RH132RoundedCoefficients14 (10^14) 40 132 s := by
      unfold E
      rw [hzero, poly60_eq_poly40]
      simp
    rw [h1, Complex.neg_im, abs_neg]
  have herr := imag_error_bound s h0 h1 ha hb
  rw [hEim] at herr
  have hpos : 0 < |s.re - 1/2| := abs_pos.mpr (sub_ne_zero.mpr hneq)
  linarith

/-- xi-to-zeta transfer (adapted from the accepted 105-106 proof). -/
lemma xi_nonzero_implies_zeta {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hXi : RH1000Analytic.CertifiedLocalXi.xi s ≠ 0) : riemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at h0
  have hs1 : s ≠ 1 := fun h => by simp [h] at h1
  have h1s : (1:ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  rw [riemannZeta_def_of_ne_zero hs0]
  intro hz
  rcases div_eq_zero_iff.mp hz with hz | hz
  · apply hXi
    have hh := completedRiemannZeta_eq s
    rw [hz] at hh
    have hsum : completedRiemannZeta₀ s = 1/s + 1/(1-s) := by
      linear_combination -hh
    unfold RH1000Analytic.CertifiedLocalXi.xi
    rw [hsum]
    field_simp
    ring
  · exact Complex.Gammaℝ_ne_zero_of_re_pos h0 hz

end Slice133

end Slice133Assembly

/-- The full 133.2-133.8 slice, statement character-identical to platform
theorem TaoFivePrimes.rh_verified_slice_133p2_133p8 (f129523d) modulo the
name `solution`. -/
theorem solution (s : ℂ) (hs : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : (666/5:ℝ) ≤ s.im) (hb : s.im ≤ (669/5:ℝ)) : s.re = 1/2 := by
  by_contra hneq
  have hxi := Slice133.xi_nonzero_off_line s h0.le h1.le ha hb hneq
  exact Slice133.xi_nonzero_implies_zeta h0 h1 hxi hs

