-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.logPshAt_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:48.434846+00:00
-- url     : https://prove2.me/submissions/81de8ed5-6fb4-4723-9ef6-59d3d42cbb35

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviChain
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_ofReal_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {φ : V n → ℝ} {x : V n} (hφ : ContDiffAt ℝ 2 φ x)
    (hL : ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun y => (φ y : ℂ)) x ξ).re) :
    LogPshAt n (fun y => Real.exp (φ y)) x := by
  have hφ1 : DifferentiableAt ℝ φ x := hφ.differentiableAt (by simp)
  have hexp : ContDiffAt ℝ 2 Real.exp (φ x) := Real.contDiff_exp.contDiffAt
  have hd1 : deriv Real.exp (φ x) = Real.exp (φ x) := by rw [Real.deriv_exp]
  have hd2 : deriv (deriv Real.exp) (φ x) = Real.exp (φ x) := by rw [Real.deriv_exp, Real.deriv_exp]
  refine ⟨(Real.exp_pos _).le, fun ξ => ?_⟩
  have hc := leviChain n Real.exp φ x ξ hφ hexp
  have hw : ∀ j, wd n j (fun y => ((Real.exp (φ y) : ℝ) : ℂ)) x =
      ((Real.exp (φ x) : ℝ) : ℂ) * wd n j (fun y => (φ y : ℂ)) x := fun j => by
    rw [wd_ofReal_comp Real.differentiable_exp.differentiableAt hφ1, hd1]
  rw [hd1, hd2] at hc
  simp only [hc, hw, mul_assoc, ← Finset.mul_sum, add_re, re_ofReal_mul, normSq_mul, normSq_ofReal,
    ofReal_re]
  set e := Real.exp (φ x)
  have he : 0 < e := Real.exp_pos _
  have hl := hL ξ
  set N := Complex.normSq (∑ j, wd n j (fun y => (φ y : ℂ)) x * ξ j)
  set R := (leviV n (fun y => (φ y : ℂ)) x ξ).re
  have hN : 0 ≤ N := Complex.normSq_nonneg _
  constructor
  · positivity
  · nlinarith [mul_nonneg (mul_nonneg he.le he.le) hl]
end ReciprocityTheory.L2DbarEstimates
