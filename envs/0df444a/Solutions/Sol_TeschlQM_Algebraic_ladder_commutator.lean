-- Prove2me | solution 1 for TeschlQM.Algebraic.ladder_commutator
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T16:32:55.517497+00:00
-- url     : https://prove2.me/submissions/999c4eb6-72fb-4a1e-9d10-ecbbe1fe2e08

import Mathlib
import Definitions.Def_TeschlQM_Algebraic_ladder

set_option autoImplicit false

namespace TeschlQM.Algebraic.P62fc348e

open TeschlQM.Algebraic

lemma core1_contDiff (ω : ℝ) (f : ℝ → ℂ) (hf : f ∈ core1 ω) : ContDiff ℝ (⊤ : ℕ∞) f := by
  unfold core1 at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k, rfl⟩ := hg
    have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => x ^ k * Real.exp (-(ω * x ^ 2) / 2)) := by
      fun_prop
    exact Complex.ofRealCLM.contDiff.comp h
  | zero => exact contDiff_const
  | add g h _ _ hg hh => exact hg.add hh
  | smul a g _ hg => exact contDiff_const.smul hg

lemma hasDerivAt_lin (s : ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ((s * y : ℝ) : ℂ)) ((s : ℝ) : ℂ) x := by
  have := ((hasDerivAt_id x).const_mul s).ofReal_comp
  simpa using this

lemma hasDerivAt_plus (ω : ℝ) (f : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) (x : ℝ) :
    HasDerivAt (ladderPlus ω f)
      (((1 / Real.sqrt 2 : ℝ) : ℂ) * ((((Real.sqrt ω : ℝ) : ℂ) * f x
        + ((Real.sqrt ω * x : ℝ) : ℂ) * deriv f x)
        - ((1 / Real.sqrt ω : ℝ) : ℂ) * deriv (deriv f) x)) x := by
  unfold ladderPlus
  have h := (((hasDerivAt_lin (Real.sqrt ω) x).mul (hf x).hasDerivAt).sub
    ((hf' x).hasDerivAt.const_mul (((1 / Real.sqrt ω : ℝ) : ℂ)))).const_mul
    (((1 / Real.sqrt 2 : ℝ) : ℂ))
  refine h.congr_deriv ?_
  ring

lemma hasDerivAt_minus (ω : ℝ) (f : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) (x : ℝ) :
    HasDerivAt (ladderMinus ω f)
      (((1 / Real.sqrt 2 : ℝ) : ℂ) * ((((Real.sqrt ω : ℝ) : ℂ) * f x
        + ((Real.sqrt ω * x : ℝ) : ℂ) * deriv f x)
        + ((1 / Real.sqrt ω : ℝ) : ℂ) * deriv (deriv f) x)) x := by
  unfold ladderMinus
  have h := (((hasDerivAt_lin (Real.sqrt ω) x).mul (hf x).hasDerivAt).add
    ((hf' x).hasDerivAt.const_mul (((1 / Real.sqrt ω : ℝ) : ℂ)))).const_mul
    (((1 / Real.sqrt 2 : ℝ) : ℂ))
  refine h.congr_deriv ?_
  ring

end TeschlQM.Algebraic.P62fc348e

open TeschlQM.Algebraic in
theorem solution (ω : ℝ) (hω : 0 < ω) (f : ℝ → ℂ) (hf : f ∈ core1 ω) :
    ladderMinus ω (ladderPlus ω f) - ladderPlus ω (ladderMinus ω f) = f := by
  have hc := TeschlQM.Algebraic.P62fc348e.core1_contDiff ω f hf
  have hd : Differentiable ℝ f := hc.differentiable (by simp)
  have hd' : Differentiable ℝ (deriv f) := by
    have := (hc.iterate_deriv 1).differentiable (by simp)
    simpa using this
  funext x
  have hP := (TeschlQM.Algebraic.P62fc348e.hasDerivAt_plus ω f hd hd' x).deriv
  have hM := (TeschlQM.Algebraic.P62fc348e.hasDerivAt_minus ω f hd hd' x).deriv
  simp only [Pi.sub_apply]
  rw [show ladderMinus ω (ladderPlus ω f) x =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt ω * x : ℝ) : ℂ) * ladderPlus ω f x
        + ((1 / Real.sqrt ω : ℝ) : ℂ) * deriv (ladderPlus ω f) x) from rfl,
    show ladderPlus ω (ladderMinus ω f) x =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt ω * x : ℝ) : ℂ) * ladderMinus ω f x
        - ((1 / Real.sqrt ω : ℝ) : ℂ) * deriv (ladderMinus ω f) x) from rfl, hP, hM]
  simp only [ladderPlus, ladderMinus]
  have h2 : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul]
    have : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
      rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
    rw [this]; push_cast; ring
  have hw : ((Real.sqrt ω : ℝ) : ℂ) * ((1 / Real.sqrt ω : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    have hs : Real.sqrt ω ≠ 0 := (Real.sqrt_pos.mpr hω).ne'
    rw [mul_one_div_cancel hs]; simp
  have hx : ((Real.sqrt ω * x : ℝ) : ℂ) = ((Real.sqrt ω : ℝ) : ℂ) * (x : ℂ) := by push_cast; ring
  rw [hx]
  linear_combination (2 * ((Real.sqrt ω : ℝ) : ℂ) * ((1 / Real.sqrt ω : ℝ) : ℂ) * f x) * h2 + f x * hw
