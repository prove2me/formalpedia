-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.shiftedTheta_eq_of_integer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:53:32.722658+00:00
-- url     : https://prove2.me/submissions/953e9399-c101-4d78-90b5-31386e719b2e

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Theorems.Thm_SharpIntermediateSubgroupBounds_summable_int_gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_shiftedTheta_summable
section
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
private lemma shifted_gaussian_fourier {A : ℝ} (hA : 0 < A) (x : ℝ) :
    (∑' z : ℤ, Real.exp (-A * ((z : ℝ) - x) ^ 2)) =
      1 / (A / Real.pi) ^ (1 / 2 : ℝ) *
        ∑' k : ℤ, Real.exp (-(Real.pi ^ 2 / A) * (k : ℝ) ^ 2) *
          Real.cos (2 * Real.pi * (k : ℝ) * x) := by
  let a : ℝ := A / Real.pi
  let b : ℝ := a * x
  have ha : 0 < a := div_pos hA Real.pi_pos
  have hP := Complex.tsum_exp_neg_quadratic
    (a := (a : ℂ)) (by simpa using ha) (b : ℂ)
  let c : ℂ := Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2)
  have hleft :
      (∑' z : ℤ, Complex.exp (-(A : ℂ) * ((z : ℂ) - (x : ℂ)) ^ 2)) =
        c * ∑' z : ℤ,
          Complex.exp (-Real.pi * (a : ℂ) * (z : ℂ) ^ 2 +
            2 * Real.pi * (b : ℂ) * (z : ℂ)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro z
    rw [← Complex.exp_add]
    congr 1
    simp only [c, a, b]
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  have hright :
      c * (1 / (a : ℂ) ^ (1 / 2 : ℂ) *
          ∑' k : ℤ, Complex.exp (-Real.pi / (a : ℂ) *
            ((k : ℂ) + Complex.I * (b : ℂ)) ^ 2)) =
        1 / (a : ℂ) ^ (1 / 2 : ℂ) *
          ∑' k : ℤ, Complex.exp
            ((-(Real.pi ^ 2 / A) * (k : ℝ) ^ 2 : ℝ) -
              (2 * Real.pi * (k : ℝ) * x : ℝ) * Complex.I) := by
    rw [← mul_assoc, mul_comm c (1 / (a : ℂ) ^ (1 / 2 : ℂ)), mul_assoc]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [← Complex.exp_add]
    congr 1
    simp only [c, a, b]
    push_cast
    field_simp [Real.pi_ne_zero, ne_of_gt hA]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hcomplex :
      (∑' z : ℤ, Complex.exp (-(A : ℂ) * ((z : ℂ) - (x : ℂ)) ^ 2)) =
        1 / (a : ℂ) ^ (1 / 2 : ℂ) *
          ∑' k : ℤ, Complex.exp
            ((-(Real.pi ^ 2 / A) * (k : ℝ) ^ 2 : ℝ) -
              (2 * Real.pi * (k : ℝ) * x : ℝ) * Complex.I) := by
    rw [hleft, hP, hright]
  have hprimalR : Summable (fun z : ℤ ↦
      Real.exp (-A * ((z : ℝ) - x) ^ 2)) := by
    simpa only [Real.log_exp] using shiftedTheta_summable
      (p := Real.exp A) (x := x) (Real.one_lt_exp_iff.mpr hA)
  have hprimalTerm (z : ℤ) :
      Complex.exp (-(A : ℂ) * ((z : ℂ) - (x : ℂ)) ^ 2) =
        (Real.exp (-A * ((z : ℝ) - x) ^ 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  have hprimalC : Summable (fun z : ℤ ↦
      Complex.exp (-(A : ℂ) * ((z : ℂ) - (x : ℂ)) ^ 2)) := by
    have hcast : Summable (fun z : ℤ ↦
        (Real.exp (-A * ((z : ℝ) - x) ^ 2) : ℂ)) :=
      Complex.summable_ofReal.mpr hprimalR
    exact hcast.congr (fun z ↦ (hprimalTerm z).symm)
  have hdual : Summable (fun k : ℤ ↦ Complex.exp
      ((-(Real.pi ^ 2 / A) * (k : ℝ) ^ 2 : ℝ) -
        (2 * Real.pi * (k : ℝ) * x : ℝ) * Complex.I)) := by
    have hg := summable_int_gaussian (A := Real.pi ^ 2 / A) (by positivity)
    refine hg.of_norm_bounded (fun k ↦ ?_)
    rw [Complex.norm_exp]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, sub_zero,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), le_refl]
  have hdualRe (k : ℤ) :
      (Complex.exp
        ((-(Real.pi ^ 2 / A) * (k : ℝ) ^ 2 : ℝ) -
          (2 * Real.pi * (k : ℝ) * x : ℝ) * Complex.I)).re =
        Real.exp (-(Real.pi ^ 2 / A) * (k : ℝ) ^ 2) *
          Real.cos (2 * Real.pi * (k : ℝ) * x) := by
    let u : ℝ := -(Real.pi ^ 2 / A) * (k : ℝ) ^ 2
    let v : ℝ := 2 * Real.pi * (k : ℝ) * x
    change (Complex.exp ((u : ℂ) - (v : ℂ) * Complex.I)).re =
      Real.exp u * Real.cos v
    simp only [Complex.exp_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, mul_one, add_zero, sub_zero, zero_sub,
      Real.cos_neg]
  have hpref : 1 / (a : ℂ) ^ (1 / 2 : ℂ) =
      ((1 / a ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    symm
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow ha.le]
    norm_num
  rw [hpref] at hcomplex
  have hre := congrArg Complex.re hcomplex
  rw [Complex.re_tsum hprimalC, Complex.mul_re, Complex.re_tsum hdual] at hre
  simpa only [hprimalTerm, Complex.ofReal_re, Complex.ofReal_im, hdualRe,
    zero_mul, sub_zero, a] using hre
end SharpIntermediateSubgroupBounds
end

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p x : ℝ} (hp : 1 < p)
    (hx : ∃ z : ℤ, (z : ℝ) = x) :
    shiftedTheta p x = gaussianTheta p := by
  obtain ⟨z, rfl⟩ := hx
  have hA : 0 < Real.log p := Real.log_pos hp
  have hzero : (∑' y : ℤ, Real.exp (-Real.log p * (y : ℝ) ^ 2)) =
      1 / (Real.log p / Real.pi) ^ (1 / 2 : ℝ) *
        ∑' k : ℤ, Real.exp (-(Real.pi ^ 2 / Real.log p) * (k : ℝ) ^ 2) := by
    simpa using shifted_gaussian_fourier hA 0
  rw [shiftedTheta, gaussianTheta, shifted_gaussian_fourier hA (z : ℝ), hzero]
  apply congrArg (fun t : ℝ ↦
    1 / (Real.log p / Real.pi) ^ (1 / 2 : ℝ) * t)
  apply tsum_congr
  intro k
  have hcos := Real.cos_int_mul_two_pi (k * z)
  have : Real.cos (2 * Real.pi * (k : ℝ) * (z : ℝ)) = 1 := by
    convert hcos using 1 <;> push_cast <;> ring
  rw [this, mul_one]
end SharpIntermediateSubgroupBounds
