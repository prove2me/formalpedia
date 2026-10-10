-- Prove2me | solution 1 for WheelerDeWittSuperspace.wdw_wkb
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T21:36:12.482681+00:00
-- url     : https://prove2.me/submissions/3b0d0f6b-875f-42ad-90e1-d3e1e6823000

import Definitions.Def_WheelerDeWittSuperspace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false

open Matrix

namespace WheelerDeWittSuperspace

/-- Derivative of the phase `i S / hbar` (as a complex function). -/
lemma hasFDerivAt_phase {X : Type*} [Fintype X] (hbar : ℝ) (f : Config X → ℝ) (h : Config X)
    (hf : DifferentiableAt ℝ f h) :
    HasFDerivAt (fun h' => Complex.I / (hbar : ℂ) * (f h' : ℂ))
      ((Complex.I / (hbar : ℂ)) • (Complex.ofRealCLM.comp (fderiv ℝ f h))) h := by
  have h1 : HasFDerivAt (fun h' => ((f h' : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ f h)) h :=
    Complex.ofRealCLM.hasFDerivAt.comp h hf.hasFDerivAt
  exact h1.const_mul (Complex.I / (hbar : ℂ))

/-- First derivative of `exp (i S / hbar)` in a coordinate direction. -/
lemma partialD_wkb {X : Type*} [Fintype X] [DecidableEq X] (hbar : ℝ) (S : Config X → ℝ)
    (hS : Differentiable ℝ S) (x : X) (c d : Fin 3) :
    partialD (fun h' => Complex.exp (Complex.I * (S h' : ℂ) / (hbar : ℂ))) x c d =
      fun h' => Complex.exp (Complex.I * (S h' : ℂ) / (hbar : ℂ)) *
        (Complex.I / (hbar : ℂ) * (partialR S x c d h' : ℂ)) := by
  funext h'
  have hE : (fun h' => Complex.exp (Complex.I * (S h' : ℂ) / (hbar : ℂ))) =
      fun h' => Complex.exp (Complex.I / (hbar : ℂ) * (S h' : ℂ)) := by
    funext y; congr 1; ring
  have := (hasFDerivAt_phase hbar S h' (hS h')).cexp
  unfold partialD partialR
  rw [hE, this.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  ring_nf

theorem wdw_wkb {X : Type*} [Fintype X] [DecidableEq X] (kappa hbar Lam : ℝ) (hkappa : kappa ≠ 0)
    (hhbar : hbar ≠ 0)
    (R : Config X → X → ℝ) (S : Config X → ℝ) (hS : ContDiff ℝ 2 S)
    (h : Config X) (x : X) :
    wdw kappa hbar Lam R (fun h' => Complex.exp (Complex.I * (S h' : ℂ) / (hbar : ℂ))) h x =
      Complex.exp (Complex.I * (S h : ℂ) / (hbar : ℂ)) *
        ((hamiltonJacobi kappa Lam R S h x : ℂ) -
          Complex.I * (hbar : ℂ) * (2 * (kappa : ℂ)) *
            ∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h x) a b c d : ℂ) *
              (partialR (partialR S x c d) x a b h : ℂ)) := by
  have hS1 : Differentiable ℝ S := hS.differentiable (by norm_num)
  have hdS : ContDiff ℝ 1 (fderiv ℝ S) := hS.fderiv_right (by norm_num)
  have hP : ∀ c d, Differentiable ℝ (partialR S x c d) := fun c d =>
    (hdS.clm_apply contDiff_const).differentiable (by norm_num)
  set E : Config X → ℂ := fun h' => Complex.exp (Complex.I * (S h' : ℂ) / (hbar : ℂ)) with hEdef
  have key : ∀ a b c d, partialD (partialD E x c d) x a b h =
      E h * (Complex.I / (hbar : ℂ) * (partialR (partialR S x c d) x a b h : ℂ) +
        (Complex.I / (hbar : ℂ)) ^ 2 * (partialR S x a b h : ℂ) * (partialR S x c d h : ℂ)) := by
    intro a b c d
    rw [hEdef, partialD_wkb hbar S hS1 x c d]
    have hE : (fun h' => Complex.exp (Complex.I * (S h' : ℂ) / (hbar : ℂ))) =
        fun h' => Complex.exp (Complex.I / (hbar : ℂ) * (S h' : ℂ)) := by
      funext y; congr 1; ring
    have h1 := (hasFDerivAt_phase hbar S h (hS1 h)).cexp
    rw [← hE] at h1
    have h2 := hasFDerivAt_phase hbar (partialR S x c d) h (hP c d h)
    have h3 := h1.mul h2
    unfold partialD
    erw [h3.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
    unfold partialR
    ring
  have hk : kinetic E h x = E h *
      (Complex.I / (hbar : ℂ) * ∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h x) a b c d : ℂ) *
          (partialR (partialR S x c d) x a b h : ℂ) +
        (Complex.I / (hbar : ℂ)) ^ 2 * ∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h x) a b c d : ℂ) *
          (partialR S x a b h : ℂ) * (partialR S x c d h : ℂ)) := by
    unfold kinetic
    rw [mul_add]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [key]
    ring
  unfold wdw hamiltonJacobi
  rw [hk]
  push_cast
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hb : (hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hhbar
  field_simp
  simp only [hEdef]
  ring_nf
  simp only [hI]
  ring

end WheelerDeWittSuperspace

open WheelerDeWittSuperspace

theorem solution {X : Type*} [Fintype X] [DecidableEq X] (kappa hbar Lam : ℝ) (hkappa : kappa ≠ 0)
    (hhbar : hbar ≠ 0)
    (R : Config X → X → ℝ) (S : Config X → ℝ) (hS : ContDiff ℝ 2 S)
    (h : Config X) (x : X) :
    wdw kappa hbar Lam R (fun h' => Complex.exp (Complex.I * (S h' : ℂ) / (hbar : ℂ))) h x =
      Complex.exp (Complex.I * (S h : ℂ) / (hbar : ℂ)) *
        ((hamiltonJacobi kappa Lam R S h x : ℂ) -
          Complex.I * (hbar : ℂ) * (2 * (kappa : ℂ)) *
            ∑ a, ∑ b, ∑ c, ∑ d, (deWitt (metricAt h x) a b c d : ℂ) *
              (partialR (partialR S x c d) x a b h : ℂ)) :=
  wdw_wkb kappa hbar Lam hkappa hhbar R S hS h x
