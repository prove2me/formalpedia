-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:04.180486+00:00
-- url     : https://prove2.me/submissions/78661492-bbfc-45ad-af44-2b1724d6579f

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IntegerToRational
open MvPolynomial
variable {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace ReciprocityTheory.AnForm.R.IntegerToRational
theorem _root_.solution : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_bot] at hx
    rw [Ideal.mem_bot]
    rcases Int.isUnit_iff.mp (hx x) with hu | hu
    · exact mul_self_eq_zero.mp (by linarith)
    · nlinarith [mul_self_nonneg x]
  · have := hP
    have : P.IsMaximal := IsPrime.to_maximal_ideal h
    exact Ideal.jacobson_eq_self_of_isMaximal
end ReciprocityTheory.AnForm.R.IntegerToRational
