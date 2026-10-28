-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_phase_132_panels
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:37:39.940238+00:00
-- url     : https://prove2.me/submissions/78a1d44a-7f69-41c5-822e-fb7b8e430ddb

import Definitions.Def_TaoFivePrimes_RHDirectPhase132
import Theorems.Thm_TaoFivePrimes_rh_direct_phase_132_seed
import Theorems.Thm_TaoFivePrimes_rh_direct_fixed_point_multiply_error
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Complex
open RHDirectPhase132

namespace DirectPhase132Panels

noncomputable def trueSquare (n : ℕ) : ℂ :=
  Complex.exp (Complex.I*((99/256*(2:ℝ)^n:ℝ):ℂ))

noncomputable def truePanel (j : ℕ) : ℂ :=
  Complex.exp (Complex.I*((66*(3*(2*(j:ℝ)+1)/16):ℝ):ℂ))

lemma square_unit (n : ℕ) : ‖trueSquare n‖=1 := by
  unfold trueSquare
  rw [Complex.norm_exp]
  have hh : (Complex.I*((99/256*(2:ℝ)^n:ℝ):ℂ)).re=0 := by
    rw [Complex.mul_re]
    simp only [Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      zero_sub, neg_zero]
  rw [hh]
  simp

lemma panel_unit (j : ℕ) : ‖truePanel j‖=1 := by
  simp [truePanel,Complex.norm_exp,Complex.mul_re]

lemma square_succ (n : ℕ) : trueSquare (n+1)=trueSquare n*trueSquare n := by
  unfold trueSquare
  rw [← Complex.exp_add]
  congr 1
  push_cast
  rw [pow_succ]
  ring

lemma panel_zero : truePanel 0=trueSquare 5 := by
  norm_num [truePanel,trueSquare]

lemma panel_succ (j : ℕ) : truePanel (j+1)=truePanel j*trueSquare 6 := by
  unfold truePanel trueSquare
  rw [← Complex.exp_add]
  congr 1
  push_cast
  norm_num
  ring

lemma rounded (p q : ℤ × ℤ) :
    ‖asComplex p*asComplex q-asComplex (multiply p q)‖ ≤ 2/10^200 := by
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  rw [norm_sub_rev]
  have hh := TaoFivePrimes.rh_direct_fixed_point_multiply_error
    (10^200) (by positivity) a b c d
  push_cast at hh
  norm_num [asComplex,multiply,scale,add_div,mul_div_assoc] at hh ⊢
  exact hh

lemma product_error (u v a b p : ℂ) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (ε η δ : ℝ) (hε : 0≤ε) (hη : 0≤η) (hδ : 0≤δ)
    (ha : ‖u-a‖≤ε) (hb : ‖v-b‖≤η) (hp : ‖a*b-p‖≤δ) :
    ‖u*v-p‖≤ε+η+ε*η+δ := by
  have haa : ‖a‖≤1+ε := by
    have hh := norm_add_le (a-u) u
    rw [sub_add_cancel,hu,norm_sub_rev] at hh
    linarith
  have hid : u*v-p=(u-a)*v+a*(v-b)+(a*b-p) := by ring
  rw [hid]
  calc
    _ ≤ ‖(u-a)*v‖+‖a*(v-b)‖+‖a*b-p‖ := (norm_add_le _ _).trans (by
      have hh := norm_add_le ((u-a)*v) (a*(v-b))
      linarith)
    _ ≤ ε+(1+ε)*η+δ := by
      have h1 : ‖(u-a)*v‖≤ε := by rw [norm_mul,hv,mul_one]; exact ha
      have h2 : ‖a*(v-b)‖≤(1+ε)*η := by
        rw [norm_mul]
        exact mul_le_mul haa hb (norm_nonneg _) (by linarith)
      linarith
    _ = _ := by ring

lemma square_step (n : ℕ) (ε : ℝ) (hε0 : 0≤ε) (hε1 : ε≤1)
    (h : ‖trueSquare n-asComplex (squares n)‖≤ε) :
    ‖trueSquare (n+1)-asComplex (squares (n+1))‖ ≤ 3*ε+2/10^200 := by
  rw [square_succ]
  change ‖trueSquare n*trueSquare n -
    asComplex (multiply (squares n) (squares n))‖ ≤ 3*ε+2/10^200
  have hp := product_error (trueSquare n) (trueSquare n) (asComplex (squares n))
    (asComplex (squares n)) (asComplex (multiply (squares n) (squares n)))
    (square_unit n) (square_unit n) ε ε (2/10^200)
    hε0 hε0 (by positivity) h h (rounded _ _)
  have he : ε*ε≤ε := by nlinarith
  linarith

lemma square_zero :
    ‖trueSquare 0-asComplex (squares 0)‖≤3/10^200 := by
  simpa [trueSquare,squares] using TaoFivePrimes.rh_direct_phase_132_seed

lemma square5 :
    ‖trueSquare 5-asComplex (squares 5)‖≤971/10^200 := by
  have h1 := square_step 0 (3/10^200) (by positivity) (by norm_num) square_zero
  have e1 : ‖trueSquare 1-asComplex (squares 1)‖≤11/10^200 := by norm_num at h1 ⊢; linarith
  have h2 := square_step 1 (11/10^200) (by positivity) (by norm_num) e1
  have e2 : ‖trueSquare 2-asComplex (squares 2)‖≤35/10^200 := by norm_num at h2 ⊢; linarith
  have h3 := square_step 2 (35/10^200) (by positivity) (by norm_num) e2
  have e3 : ‖trueSquare 3-asComplex (squares 3)‖≤107/10^200 := by norm_num at h3 ⊢; linarith
  have h4 := square_step 3 (107/10^200) (by positivity) (by norm_num) e3
  have e4 : ‖trueSquare 4-asComplex (squares 4)‖≤323/10^200 := by norm_num at h4 ⊢; linarith
  have h5 := square_step 4 (323/10^200) (by positivity) (by norm_num) e4
  norm_num at h5 ⊢
  linarith

lemma square6 :
    ‖trueSquare 6-asComplex (squares 6)‖≤2915/10^200 := by
  have h6 := square_step 5 (971/10^200) (by positivity) (by norm_num) square5
  norm_num at h6 ⊢
  linarith

lemma panel_step (j : ℕ) (ε : ℝ) (hε0 : 0≤ε) (hε1 : ε≤1)
    (h : ‖truePanel j-asComplex (panels j)‖≤ε) :
    ‖truePanel (j+1)-asComplex (panels (j+1))‖≤ε+5832/10^200 := by
  rw [panel_succ]
  change ‖truePanel j*trueSquare 6 -
    asComplex (multiply (panels j) (squares 6))‖≤ε+5832/10^200
  have hp := product_error (truePanel j) (trueSquare 6) (asComplex (panels j))
    (asComplex (squares 6)) (asComplex (multiply (panels j) (squares 6)))
    (panel_unit j) (square_unit 6) ε (2915/10^200) (2/10^200)
    hε0 (by positivity) (by positivity) h square6 (rounded _ _)
  have he : ε*(2915/10^200) ≤ 2915/10^200 := by
    nlinarith
  linarith

lemma panel_bound (j : ℕ) (hj : j≤15) :
    ‖truePanel j-asComplex (panels j)‖≤(971+5832*(j:ℝ))/10^200 := by
  induction j with
  | zero => simpa [panel_zero,panels] using square5
  | succ j ih =>
    have hj' : j≤15 := by omega
    have hjR : (j:ℝ)≤15 := by exact_mod_cast hj'
    have hε0 : 0≤(971+5832*(j:ℝ))/10^200 := by positivity
    have hε1 : (971+5832*(j:ℝ))/10^200≤1 := by
      norm_num
      linarith
    have hh := panel_step j _ hε0 hε1 (ih hj')
    have he : (971+5832*(j:ℝ))/10^200+5832/10^200 =
        (971+5832*((j+1:ℕ):ℝ))/10^200 := by push_cast; ring
    rwa [he] at hh

end DirectPhase132Panels

/-- Certified fixed-point approximations to all sixteen phases at height 132. -/
theorem solution (j : ℕ) (hj : j<16) :
    ‖Complex.exp (Complex.I*((66*(3*(2*(j:ℝ)+1)/16):ℝ):ℂ)) -
      RHDirectPhase132.asComplex (RHDirectPhase132.panels j)‖ ≤ 1/10^194 := by
  have hj' : j≤15 := by omega
  have hjR : (j:ℝ)≤15 := by exact_mod_cast hj'
  have h := DirectPhase132Panels.panel_bound j hj'
  change ‖Complex.exp (Complex.I*((66*(3*(2*(j:ℝ)+1)/16):ℝ):ℂ)) -
      RHDirectPhase132.asComplex (RHDirectPhase132.panels j)‖ ≤
        (971+5832*(j:ℝ))/10^200 at h
  apply h.trans
  norm_num
  linarith
