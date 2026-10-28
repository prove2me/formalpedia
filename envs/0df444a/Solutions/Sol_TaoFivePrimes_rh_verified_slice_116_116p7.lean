-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_slice_116_116p7
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:58:23.812045+00:00
-- url     : https://prove2.me/submissions/73cb361c-16bd-40c6-92b2-a1b32c8cea10

/- Critical-line verification from a local xi approximation and an exact
imaginary-part certificate. The analytic projection argument is adapted from
Prove2Me submission 016f4991-59da-4657-a24d-de763fabf1a4 by sometik179;
theta/Mellin foundations are due to Gabewhigham. -/
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.MellinTransform
import Theorems.Thm_TaoFivePrimes_rh114p5_xi_approximation
import Theorems.Thm_TaoFivePrimes_rh116to116p7_imaginary_certificate

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Complex Metric Set MeasureTheory HurwitzZeta Finset
open scoped ComplexConjugate

namespace RH114SliceB

noncomputable def P : WeakFEPair ℂ := hurwitzEvenFEPair 0

private lemma f_modif_of_one_lt {t : ℝ} (ht : 1 < t) :
    P.f_modif t = ((evenKernel 0 t : ℝ) : ℂ) - 1 := by
  simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, ht, not_lt.2 ht.le, Set.indicator_of_notMem]

private lemma f_modif_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    P.f_modif t = ((evenKernel 0 t : ℝ) : ℂ) - ((t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
  simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, h0, h1, not_lt.2 h1.le]
  norm_num

private lemma f_modif_one : P.f_modif 1 = 0 := by
  simp [P, WeakFEPair.f_modif]

private lemma conj_kernel {t : ℝ} (ht : 0 < t) : conj (P.f_modif t) = P.f_modif t := by
  rcases lt_trichotomy t 1 with h | rfl | h
  · rw [f_modif_of_lt_one ht h]
    simp
  · rw [f_modif_one]
    simp
  · rw [f_modif_of_one_lt h]
    simp

private lemma completedZeta_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  change mellin P.f_modif (conj s / 2) / 2 = conj (mellin P.f_modif (s / 2) / 2)
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

noncomputable def center (T : ℝ) : ℂ := 1/2+(T:ℂ)*I
noncomputable def xi (s : ℂ) : ℂ := RH1000Analytic.CertifiedLocalXi.xi s
noncomputable def polynomial (s : ℂ) : ℂ :=
  TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH114p5RoundedCoefficients 40 (229/2) s

private lemma polynomial_eq (s : ℂ) :
    TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH114p5RoundedCoefficients 60 (229/2) s =
      TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH114p5RoundedCoefficients 40 (229/2) s := by
  unfold TaoFivePrimes_RHLocalRoundedPolynomial
  symm
  apply Finset.sum_subset (Finset.range_mono (by norm_num : 40 ≤ 60))
  intro n hn60 hn40
  have hge : 40 ≤ n := by simp only [Finset.mem_range] at hn40; omega
  have hz : TaoFivePrimes_RH114p5RoundedCoefficients.getD n 0 = 0 := by
    apply List.getD_eq_default
    have hlen : TaoFivePrimes_RH114p5RoundedCoefficients.length = 40 := by
      norm_num [TaoFivePrimes_RH114p5RoundedCoefficients]
    omega
  rw [hz]
  norm_num

private lemma xi_entire : Differentiable ℂ xi := by
  unfold xi RH1000Analytic.CertifiedLocalXi.xi
  have hΛ := differentiable_completedZeta₀
  fun_prop

private lemma polynomial_entire : Differentiable ℂ polynomial := by
  unfold polynomial TaoFivePrimes_RHLocalRoundedPolynomial RH1000Analytic.CertifiedLocalXi.center
  fun_prop

private lemma xi_critical_real (T : ℝ) : (xi (center T)).im = 0 := by
  have hc : conj (center T) = 1-center T := by
    apply Complex.ext <;> simp [center]
    ring
  have he := completedZeta_conj (center T)
  rw [hc,completedRiemannZeta₀_one_sub] at he
  have hi := congrArg Complex.im he
  simp only [conj_im] at hi
  have hΛ : (completedRiemannZeta₀ (center T)).im = 0 := by linarith
  have hf : (center T*(center T-1)/2).im = 0 := by
    norm_num [center,mul_im]
    ring
  unfold xi RH1000Analytic.CertifiedLocalXi.xi
  simp [mul_im,hf,hΛ]

private lemma polynomial_critical_real (y : ℝ) : (polynomial (center y)).im = 0 := by
  have hv : -I*(center y-RH1000Analytic.CertifiedLocalXi.center (229/2)) =
      ((y-229/2:ℝ):ℂ) := by
    apply Complex.ext <;> simp [center,RH1000Analytic.CertifiedLocalXi.center] <;> ring
  have he : polynomial (center y) =
      ((∑ n ∈ range 40,
        ((TaoFivePrimes_RH114p5RoundedCoefficients.getD n 0:ℝ)/(10^8:ℝ))*(y-229/2)^n : ℝ):ℂ) := by
    unfold polynomial TaoFivePrimes_RHLocalRoundedPolynomial
    rw [hv]
    push_cast
    rfl
  rw [he]
  exact Complex.ofReal_im _

private lemma coefficient_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ)
    (R M : ℝ) (hR : 0 < R) (hb : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖iteratedDeriv n f c / (n.factorial:ℂ)‖ ≤ M/R^n := by
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf.diffContOnCl hb
  rw [norm_div,Complex.norm_natCast]
  have hn : (0:ℝ) < n.factorial := by positivity
  apply (div_le_iff₀ hn).mpr
  calc
    ‖iteratedDeriv n f c‖ ≤ n.factorial*M/R^n := hd
    _ = M/R^n*n.factorial := by ring

private lemma deriv_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ)
    (hb : ∀ z, ‖z-c‖ ≤ 5/2 → ‖f z‖ ≤ 3/4) (z : ℂ) (hz : ‖z-c‖ ≤ 23/10) :
    ‖deriv f z‖ ≤ 8 := by
  have hcircle : ∀ w ∈ sphere z (1/10:ℝ), ‖f w‖ ≤ 3/4 := by
    intro w hw
    apply hb
    calc
      ‖w-c‖ = ‖(w-z)+(z-c)‖ := by congr 1; ring
      _ ≤ ‖w-z‖+‖z-c‖ := norm_add_le _ _
      _ ≤ 5/2 := by rw [mem_sphere_iff_norm.mp hw]; linarith
  have h := coefficient_bound f hf z (1/10) (3/4) (by norm_num) hcircle 1
  norm_num at h
  linarith

private lemma critical_projection_distance (z : ℂ) : ‖z-center z.im‖ = |z.re-1/2| := by
  have he : z-center z.im = ((z.re-1/2:ℝ):ℂ) := by
    apply Complex.ext <;> simp [center]
  rw [he,Complex.norm_real,Real.norm_eq_abs]

private lemma critical_projection_in_ball (T : ℝ) (z : ℂ) :
    ‖center z.im-center T‖ ≤ ‖z-center T‖ := by
  have he : center z.im-center T = ((z.im-T:ℝ):ℂ)*I := by unfold center; push_cast; ring
  rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  simpa [center] using Complex.abs_im_le_norm (z-center T)

private lemma rectangle_in_ball (z : ℂ) (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1)
    (ha : (116:ℝ) ≤ z.im) (hb : z.im ≤ (1167/10:ℝ)) :
    ‖z-center (229/2)‖ ≤ 23/10 := by
  have hx : |z.re-1/2| ≤ 1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hy : |z.im-229/2| ≤ 11/5 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hx2 : (z.re-1/2)^2 ≤ (1/2:ℝ)^2 := by nlinarith [abs_nonneg (z.re-1/2),sq_abs (z.re-1/2)]
  have hy2 : (z.im-229/2)^2 ≤ (11/5:ℝ)^2 := by nlinarith [abs_nonneg (z.im-229/2),sq_abs (z.im-229/2)]
  have hn : ‖z-center (229/2)‖^2 = (z.re-1/2)^2+(z.im-229/2)^2 := by
    rw [←Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply,center,pow_two]
  nlinarith [norm_nonneg (z-center (229/2))]

private lemma xi_nonzero_implies_zeta {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hXi : xi s ≠ 0) : riemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at h0
  have hs1 : s ≠ 1 := fun h => by simp [h] at h1
  have h1s : (1:ℂ)-s ≠ 0 := sub_ne_zero.mpr hs1.symm
  rw [riemannZeta_def_of_ne_zero hs0]
  intro hz
  rcases div_eq_zero_iff.mp hz with hz | hz
  · apply hXi
    have hh := completedRiemannZeta_eq s
    rw [hz] at hh
    have hsum : completedRiemannZeta₀ s=1/s+1/(1-s) := by linear_combination -hh
    unfold xi RH1000Analytic.CertifiedLocalXi.xi
    rw [hsum]
    field_simp
    ring
  · exact Complex.Gammaℝ_ne_zero_of_re_pos h0 hz

end RH114SliceB

theorem solution (s : ℂ) (hs : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : (116:ℝ) ≤ s.im) (hb : s.im ≤ (1167/10:ℝ)) : s.re = 1/2 := by
  by_contra hneq
  let f : ℂ → ℂ := fun z => ((10^37:ℕ):ℂ)*RH114SliceB.xi z-RH114SliceB.polynomial z
  have hf : Differentiable ℂ f := RH114SliceB.xi_entire.const_mul _ |>.sub RH114SliceB.polynomial_entire
  have hball : ∀ z, ‖z-RH114SliceB.center (229/2)‖ ≤ 5/2 → ‖f z‖ ≤ 3/4 := by
    intro z hz
    have he := TaoFivePrimes.rh114p5_xi_approximation z
      (by simpa [RH114SliceB.center,RH1000Analytic.CertifiedLocalXi.center] using hz)
    rw [RH114SliceB.polynomial_eq] at he
    exact he
  have hz := RH114SliceB.rectangle_in_ball s h0.le h1.le ha hb
  have hw := (RH114SliceB.critical_projection_in_ball (229/2) s).trans hz
  have hl := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hf x)
    (fun x hx => RH114SliceB.deriv_bound f hf (RH114SliceB.center (229/2)) hball x (mem_closedBall_iff_norm.mp hx))
    (convex_closedBall (RH114SliceB.center (229/2)) (23/10))
    (mem_closedBall_iff_norm.mpr hw) (mem_closedBall_iff_norm.mpr hz)
  rw [RH114SliceB.critical_projection_distance] at hl
  have hcritical : (f (RH114SliceB.center s.im)).im = 0 := by
    dsimp [f]
    simp [Complex.mul_im,RH114SliceB.xi_critical_real,RH114SliceB.polynomial_critical_real]
  have hi : |(f s).im| ≤ 8*|s.re-1/2| := by
    have he : (f s).im = (f s-f (RH114SliceB.center s.im)).im := by
      have hh : (f s-f (RH114SliceB.center s.im)).im = (f s).im := by
        change (f s).im-(f (RH114SliceB.center s.im)).im = (f s).im
        rw [hcritical,sub_zero]
      exact hh.symm
    rw [he]
    exact (Complex.abs_im_le_norm _).trans hl
  have hXi : RH114SliceB.xi s = 0 := by
    by_contra hn
    exact RH114SliceB.xi_nonzero_implies_zeta h0 h1 hn hs
  have hcert := TaoFivePrimes.rh116to116p7_imaginary_certificate s h0.le h1.le ha hb
  have heq : |(f s).im| = |(RH114SliceB.polynomial s).im| := by
    simp [f,hXi]
  rw [heq] at hi
  have hp : 0 < |s.re-1/2| := abs_pos.mpr (sub_ne_zero.mpr hneq)
  change 12*|s.re-1/2| ≤ |(RH114SliceB.polynomial s).im| at hcert
  linarith
