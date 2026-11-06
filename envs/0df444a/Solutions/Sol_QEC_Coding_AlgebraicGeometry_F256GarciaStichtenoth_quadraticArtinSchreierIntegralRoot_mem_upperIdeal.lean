-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierIntegralRoot_mem_upperIdeal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:51:07.265813+00:00
-- url     : https://prove2.me/submissions/985c981d-073e-4ead-837b-ed8bfc2a8785

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralUniformizer_mem_upperIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralRoot_equation

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    quadraticArtinSchreierIntegralRoot P a ha ∈
      quadraticArtinSchreierUpperIdeal P a ha := by
  let Q := quadraticArtinSchreierUpperIdeal P a ha
  let w := quadraticArtinSchreierIntegralRoot P a ha
  let t := quadraticArtinSchreierIntegralUniformizer P a ha
  have ht : t ∈ Q :=
    quadraticArtinSchreierIntegralUniformizer_mem_upperIdeal P a ha
  have hterm : t * w ∈ Q := Q.mul_mem_right _ ht
  have hrest : t * w + t ∈ Q := Q.add_mem hterm ht
  have heq : w ^ 2 + t * w + t = 0 :=
    quadraticArtinSchreierIntegralRoot_equation P a ha
  have hw2eq : w ^ 2 = -(t * w + t) := by
    linear_combination heq
  have hw2 : w ^ 2 ∈ Q := hw2eq.symm ▸ Q.neg_mem hrest
  exact (quadraticArtinSchreierUpperIdeal_isMaximal P a ha).isPrime.mem_of_pow_mem
    2 hw2
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
