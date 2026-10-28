-- Prove2me | solution 1 for TaoFivePrimes.oscillatory_smoothed_zero_kernel_bound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:36:11.993786+00:00
-- url     : https://prove2.me/submissions/861abe26-4e2d-4e6d-ae37-4d086eba2661

-- The kernel and normalized estimate are published Prove2Me inputs.
import Definitions.Def_dusart_psi_433_20261014_SmoothedFormula
import Theorems.Thm_TaoFivePrimes_normalized_oscillatory_second_difference
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex

private lemma positive_cpow_split (v : ℝ) (hv : 0 < v) (s : ℂ) :
    (v:ℂ)^s = ((v^s.re:ℝ):ℂ) *
      Complex.exp (((s.im*Real.log v:ℝ):ℂ)*Complex.I) := by
  have hv' : (v:ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [Complex.cpow_def_of_ne_zero hv', ← Complex.ofReal_log hv.le]
  have he : ((Real.log v:ℝ):ℂ)*s =
      ((Real.log v*s.re:ℝ):ℂ)+(((s.im*Real.log v:ℝ):ℂ)*Complex.I) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hv]

theorem solution (a h : ℝ) (ρ : ℂ) (ha : 0 < a) (hh : 0 < h) (hsmall : 2*h ≤ a)
    (hβ0 : 0 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) (hγ : 0 < |ρ.im|) :
    ‖DusartSmoothing.smoothedZeroKernel a h ρ‖ ≤
      (a+2*h)^(ρ.re+2)/(h^2*|ρ.im|^3) *
        (4*(Real.sin (ρ.im*(h/(a+h))/2))^2 + 8*(h/(a+h)) +
          3 * |ρ.im| * (h/(a+h))^2) := by
  let m : ℝ := a+h
  let r : ℝ := h/m
  let α : ℝ := ρ.re+2
  let γ : ℝ := ρ.im
  let F : ℝ := 4*(Real.sin (γ*r/2))^2+8*r+3 * |γ| * r^2
  have hm : 0 < m := by dsimp [m]; linarith
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1/3 := by
    dsimp [r]
    apply (div_le_iff₀ hm).2
    dsimp [m] at *
    linarith
  have hα0 : 0 ≤ α := by dsimp [α]; linarith
  have hα3 : α ≤ 3 := by dsimp [α]; linarith
  have hp : 0 < 1+r := by linarith
  have hn : 0 < 1-r := by linarith
  have hs := TaoFivePrimes.normalized_oscillatory_second_difference r α γ hr0 hr1 hα0 hα3
  have hplus : m*(1+r)=a+2*h := by dsimp [m,r]; field_simp; ring
  have hminus : m*(1-r)=a := by dsimp [m,r]; field_simp; ring
  have hpluspow : ((a+2*h:ℝ):ℂ)^(ρ+2) = (m:ℂ)^(ρ+2) *
      (((1+r)^α:ℝ):ℂ)*Complex.exp (((γ*Real.log (1+r):ℝ):ℂ)*Complex.I) := by
    rw [← hplus, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hm.le hp.le,
      positive_cpow_split (1+r) hp (ρ+2)]
    simp only [Complex.add_re, Complex.add_im, Complex.re_ofNat, Complex.im_ofNat, add_zero]
    dsimp [α,γ]
    ring
  have hminuspow : (a:ℂ)^(ρ+2) = (m:ℂ)^(ρ+2) *
      (((1-r)^α:ℝ):ℂ)*Complex.exp (((γ*Real.log (1-r):ℝ):ℂ)*Complex.I) := by
    rw [← hminus, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hm.le hn.le,
      positive_cpow_split (1-r) hn (ρ+2)]
    simp only [Complex.add_re, Complex.add_im, Complex.re_ofNat, Complex.im_ofNat, add_zero]
    dsimp [α,γ]
    ring
  let N : ℂ := ((a+2*h:ℝ):ℂ)^(ρ+2)-2*(m:ℂ)^(ρ+2)+(a:ℂ)^(ρ+2)
  let Q : ℂ := ρ*(ρ+1)*(ρ+2)
  have hN : N = (m:ℂ)^(ρ+2)*
      ((((1+r)^α:ℝ):ℂ)*Complex.exp (((γ*Real.log (1+r):ℝ):ℂ)*Complex.I)-2+
       (((1-r)^α:ℝ):ℂ)*Complex.exp (((γ*Real.log (1-r):ℝ):ℂ)*Complex.I)) := by
    dsimp [N]
    rw [hpluspow,hminuspow]
    ring
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hmz : m^α ≤ (a+2*h)^α := by
    apply Real.rpow_le_rpow (by linarith [hm]) (by dsimp [m]; linarith) hα0
  have hnorm : ‖N‖ ≤ (a+2*h)^α * F := by
    rw [hN, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hm]
    simp only [Complex.add_re, Complex.re_ofNat]
    change m^α * _ ≤ _
    exact (mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hm.le α)).trans
      (mul_le_mul_of_nonneg_right hmz hF)
  have h0 := Complex.abs_im_le_norm ρ
  have h1 : |ρ.im| ≤ ‖ρ+1‖ := by simpa using (Complex.abs_im_le_norm (ρ+1))
  have h2 : |ρ.im| ≤ ‖ρ+2‖ := by simpa using (Complex.abs_im_le_norm (ρ+2))
  have hQ : |ρ.im|^3 ≤ ‖Q‖ := by
    dsimp [Q]
    rw [norm_mul,norm_mul]
    calc
      |ρ.im|^3 = |ρ.im| * |ρ.im| * |ρ.im| := by ring
      _ ≤ ‖ρ‖*‖ρ+1‖*‖ρ+2‖ := by gcongr
  have hkernel : DusartSmoothing.quadraticKernel (a+2*h) ρ -
      2*DusartSmoothing.quadraticKernel (a+h) ρ +
      DusartSmoothing.quadraticKernel a ρ = N/Q := by
    dsimp [DusartSmoothing.quadraticKernel,N,Q,m]
    ring
  have hzF : 0 ≤ (a+2*h)^α*F := by positivity
  have hdiv : ‖N‖/‖Q‖ ≤ ((a+2*h)^α*F)/|ρ.im|^3 :=
    div_le_div₀ hzF hnorm (pow_pos hγ 3) hQ
  rw [DusartSmoothing.smoothedZeroKernel,hkernel,norm_div,norm_div,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
  calc
    _ ≤ (((a+2*h)^α*F)/|ρ.im|^3)/h^2 := div_le_div_of_nonneg_right hdiv (sq_nonneg h)
    _ = _ := by dsimp [α,γ,F,r,m]; ring
