-- Prove2me | solution 1 for RHInBoxAnalytic.rect_winding_generic
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:33:15.076648+00:00
-- url     : https://prove2.me/submissions/8c38856f-e15e-4931-b453-b3a2994ee9f2

import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Mathlib
/- Task 2 (parameterized RH-in-a-box): generalize the zeta Blaschke split + box argument
   principle from the merged FIXED ball `ball cB 13` / fixed corners to an ARBITRARY box
   `[sigma0, sigma1] x [T0, T1]` with a VARIABLE Blaschke ball `(c, R)`, the geometry entering
   only as hypotheses `hRpos`, `hbox_ball`, `hs1` (and the box-ordering `hsig`, `hT`).

   This file reproduces, over variable corners and a variable ball, the three merged atoms
     - the per-pole interior winding `Bd((z-ρ)^{-1}) = 2*pi*I` (branch-split primitive),
     - the residue-sum linearity `Bd(∑ d/(z-ρ)) = 2*pi*I*∑ d`,
     - the analytic E-arg-principle `Bd(E) = 0` (Mathlib `integral_boundary_rect_eq_zero...`),
   and the KERNEL-DERIVED local Blaschke split of `logDeriv riemannZeta` over the variable ball
   (`MeromorphicOn.extract_zeros_poles`, E-holomorphicity in-kernel), then composes them into
     `RHInBoxAnalytic.zeta_count_eq_winding_generic`:
   the actual divisor of `riemannZeta` over `ball c R` is nonneg, captures every box zero, and its
   total equals the Arb winding integer `N` (derived from `hwind` via the argument principle).

   Divisor-support finiteness is obtained from `IsCompact.inter_riemannZetaZeros_finite`
   (compact `closedBall c R` meets `riemannZetaZeros` finitely), NOT from meromorphy on the closed
   ball -- so no assumption is needed about the pole `1` on the closed-ball boundary; only
   `1 ∉ ball c R` (open) enters, exactly as the brief requires.

   conjecture1_proved = False.  This is a kernel derivation of a parameterized argument-principle
   count; it does NOT prove RH. -/


open Complex Filter MeasureTheory Real
open scoped Topology

namespace RHInBoxAnalytic

/-! ## Part A: function-agnostic log-derivative transfer across a codiscrete equality.
    (Verbatim from the merged `BlaschkeBox.lean`; pure Mathlib, function-agnostic.) -/







/-! ## Part B: log-derivative of the factorized-rational product.  (Verbatim.) -/





/-! ## Part C: `riemannZeta` meromorphic-order facts on `{1}ᶜ`.  (Verbatim from merged.) -/



/-! ## Part D: generic per-pole interior winding and residue-sum atoms over variable corners.

    Generalizes `WindingCount.winding_lambda_five_rect_winding` and
    `BoxArgPrinciple.box_residue_sum_lambda` from the fixed corners `2/5,3/5,10,35` to variable
    `sigma0 < ρ.re < sigma1`, `T0 < ρ.im < T1`. -/

/-- Monodromy jump `log(-x) - log x = pi*i` when `Im x < 0` (principal branch). -/
theorem log_neg_sub_im_neg (x : ℂ) (hx : x.im < 0) :
    Complex.log (-x) - Complex.log x = ↑π * I := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hx]

/-- Monodromy jump `log(-x) - log x = -(pi*i)` when `Im x > 0` (principal branch). -/
theorem log_neg_sub_im_pos (x : ℂ) (hx : 0 < x.im) :
    Complex.log (-x) - Complex.log x = -(↑π * I) := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re, norm_neg]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hx]







/-! ## Part E: variable-ball local Blaschke split of `logDeriv riemannZeta`.

    Generalizes `BlaschkeBox.zeta_blaschke_split_box` to an arbitrary ball `(c, R)` whose interior
    avoids `1` (`hs1`) and whose box `[σ0,σ1]x[T0,T1] ⊆ ball c R` (`hbox_ball`).  Divisor
    finiteness comes from `IsCompact.inter_riemannZetaZeros_finite`. -/









/-! ## Part F: the parameterized capstone. -/



end RHInBoxAnalytic


/- Task 2 (parameterized RH-in-a-box): generalize the zeta Blaschke split + box argument
   principle from the merged FIXED ball `ball cB 13` / fixed corners to an ARBITRARY box
   `[sigma0, sigma1] x [T0, T1]` with a VARIABLE Blaschke ball `(c, R)`, the geometry entering
   only as hypotheses `hRpos`, `hbox_ball`, `hs1` (and the box-ordering `hsig`, `hT`).

   This file reproduces, over variable corners and a variable ball, the three merged atoms
     - the per-pole interior winding `Bd((z-ρ)^{-1}) = 2*pi*I` (branch-split primitive),
     - the residue-sum linearity `Bd(∑ d/(z-ρ)) = 2*pi*I*∑ d`,
     - the analytic E-arg-principle `Bd(E) = 0` (Mathlib `integral_boundary_rect_eq_zero...`),
   and the KERNEL-DERIVED local Blaschke split of `logDeriv riemannZeta` over the variable ball
   (`MeromorphicOn.extract_zeros_poles`, E-holomorphicity in-kernel), then composes them into
     `RHInBoxAnalytic.zeta_count_eq_winding_generic`:
   the actual divisor of `riemannZeta` over `ball c R` is nonneg, captures every box zero, and its
   total equals the Arb winding integer `N` (derived from `hwind` via the argument principle).

   Divisor-support finiteness is obtained from `IsCompact.inter_riemannZetaZeros_finite`
   (compact `closedBall c R` meets `riemannZetaZeros` finitely), NOT from meromorphy on the closed
   ball -- so no assumption is needed about the pole `1` on the closed-ball boundary; only
   `1 ∉ ball c R` (open) enters, exactly as the brief requires.

   conjecture1_proved = False.  This is a kernel derivation of a parameterized argument-principle
   count; it does NOT prove RH. -/


open Complex Filter MeasureTheory Real
open scoped Topology

section
namespace RHInBoxAnalytic
end RHInBoxAnalytic
open RHInBoxAnalytic

/-! ## Part A: function-agnostic log-derivative transfer across a codiscrete equality.
    (Verbatim from the merged `BlaschkeBox.lean`; pure Mathlib, function-agnostic.) -/







/-! ## Part B: log-derivative of the factorized-rational product.  (Verbatim.) -/





/-! ## Part C: `riemannZeta` meromorphic-order facts on `{1}ᶜ`.  (Verbatim from merged.) -/



/-! ## Part D: generic per-pole interior winding and residue-sum atoms over variable corners.

    Generalizes `WindingCount.winding_lambda_five_rect_winding` and
    `BoxArgPrinciple.box_residue_sum_lambda` from the fixed corners `2/5,3/5,10,35` to variable
    `sigma0 < ρ.re < sigma1`, `T0 < ρ.im < T1`. -/






theorem solution
    (sigma0 sigma1 T0 T1 : ℝ) (ρ : ℂ)
    (hre0 : sigma0 < ρ.re) (hre1 : ρ.re < sigma1)
    (him0 : T0 < ρ.im) (him1 : ρ.im < T1) :
    (∫ x in sigma0..sigma1, ((↑x + (T0 : ℂ) * I) - ρ)⁻¹)
        - (∫ x in sigma0..sigma1, ((↑x + (T1 : ℂ) * I) - ρ)⁻¹)
        + I • (∫ y in T0..T1, (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹)
        - I • (∫ y in T0..T1, (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹)
      = 2 * ↑π * I := by
  have hσ : sigma0 ≤ sigma1 := le_of_lt (lt_trans hre0 hre1)
  have hTle : T0 ≤ T1 := le_of_lt (lt_trans him0 him1)
  have horiz : ∀ c : ℂ, (∀ x : ℝ, ((↑x + c) - ρ).im ≠ 0) →
      (∫ x in sigma0..sigma1, ((↑x + c) - ρ)⁻¹)
        = Complex.log ((↑sigma1 + c) - ρ) - Complex.log ((↑sigma0 + c) - ρ) := by
    intro c hc
    have hderiv : ∀ x ∈ Set.uIcc sigma0 sigma1,
        HasDerivAt (fun x : ℝ => Complex.log ((↑x + c) - ρ)) (((↑x + c) - ρ)⁻¹) x := by
      intro x _
      have hpath : HasDerivAt (fun x : ℝ => ((↑x : ℂ) + c) - ρ) 1 x := by
        have h1 : HasDerivAt (fun x : ℝ => (↑x : ℂ)) 1 x := by simpa using (hasDerivAt_id x).ofReal_comp
        exact (h1.add_const c).sub_const ρ
      have hslit : ((↑x + c) - ρ) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; exact Or.inr (hc x)
      have hd := hpath.clog_real hslit
      rwa [one_div] at hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    apply Continuous.intervalIntegrable
    refine Continuous.inv₀ (by fun_prop) (fun x => ?_)
    rw [sub_ne_zero]; intro h
    exact hc x (by rw [h]; simp)
  have vert : ∀ c : ℂ, (∀ y : ℝ, ((c + ↑y * I) - ρ) ∈ Complex.slitPlane) →
      I • (∫ y in T0..T1, ((c + ↑y * I) - ρ)⁻¹)
        = Complex.log ((c + ↑T1 * I) - ρ) - Complex.log ((c + ↑T0 * I) - ρ) := by
    intro c hslit
    rw [← intervalIntegral.integral_smul]
    have hderiv : ∀ y ∈ Set.uIcc T0 T1,
        HasDerivAt (fun y : ℝ => Complex.log ((c + ↑y * I) - ρ)) (I • ((c + ↑y * I) - ρ)⁻¹) y := by
      intro y _
      have hpath : HasDerivAt (fun y : ℝ => (c + (↑y : ℂ) * I) - ρ) I y := by
        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I
        exact (h2.const_add c).sub_const ρ
      have hd := hpath.clog_real (hslit y)
      rwa [div_eq_mul_inv, ← smul_eq_mul] at hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    apply Continuous.intervalIntegrable
    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I
    have := hslit y
    rw [Complex.mem_slitPlane_iff] at this
    intro h; rw [h] at this; simp at this
  have hbot := horiz ((T0 : ℂ) * I) (by
    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith)
  have htop := horiz ((T1 : ℂ) * I) (by
    intro x; simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith)
  have hright := vert ((sigma1 : ℝ) : ℂ) (by
    intro y; rw [Complex.mem_slitPlane_iff]; left
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]; simp; linarith)
  have hleftJ : I • (∫ y in T0..T1, (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹)
      = Complex.log (ρ - ((sigma0 : ℂ) + ↑T1 * I)) - Complex.log (ρ - ((sigma0 : ℂ) + ↑T0 * I)) := by
    rw [← intervalIntegral.integral_smul]
    have hderiv : ∀ y ∈ Set.uIcc T0 T1,
        HasDerivAt (fun y : ℝ => Complex.log (ρ - ((sigma0 : ℂ) + ↑y * I)))
          (I • (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹) y := by
      intro y _
      have hpath : HasDerivAt (fun y : ℝ => ρ - ((sigma0 : ℂ) + (↑y : ℂ) * I)) (-I) y := by
        have h1 : HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
        have h2 : HasDerivAt (fun y : ℝ => (↑y : ℂ) * I) I y := by simpa using h1.mul_const I
        exact (h2.const_add ((sigma0 : ℂ))).const_sub ρ
      have hslit : (ρ - ((sigma0 : ℂ) + ↑y * I)) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; left
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im]; simp; linarith
      have hd := hpath.clog_real hslit
      have hval : (-I) / (ρ - ((sigma0 : ℂ) + ↑y * I)) = I • (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹ := by
        rw [smul_eq_mul, div_eq_mul_inv,
          show ρ - ((sigma0 : ℂ) + ↑y * I) = -(((sigma0 : ℂ) + ↑y * I) - ρ) from by ring, inv_neg]
        ring
      rwa [hval] at hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ?_]
    apply Continuous.intervalIntegrable
    refine (Continuous.inv₀ (by fun_prop) (fun y => ?_)).const_smul I
    rw [sub_ne_zero]; intro h
    have : (((sigma0 : ℂ) + ↑y * I)).re = ρ.re := by rw [h]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im] at this; simp at this; linarith
  rw [hbot, htop, hright, hleftJ,
    show ρ - ((sigma0 : ℂ) + ↑T1 * I) = -((↑sigma0 + (T1 : ℂ) * I) - ρ) from by ring,
    show ρ - ((sigma0 : ℂ) + ↑T0 * I) = -((↑sigma0 + (T0 : ℂ) * I) - ρ) from by ring]
  have hAim : ((↑sigma0 + (T0 : ℂ) * I) - ρ).im < 0 := by
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith
  have hDim : 0 < ((↑sigma0 + (T1 : ℂ) * I) - ρ).im := by
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; simp; linarith
  linear_combination log_neg_sub_im_neg ((↑sigma0 + (T0 : ℂ) * I) - ρ) hAim
    - log_neg_sub_im_pos ((↑sigma0 + (T1 : ℂ) * I) - ρ) hDim
