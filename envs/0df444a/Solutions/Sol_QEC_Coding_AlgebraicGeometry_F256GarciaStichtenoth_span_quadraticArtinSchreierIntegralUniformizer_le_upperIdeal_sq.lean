-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.span_quadraticArtinSchreierIntegralUniformizer_le_upperIdeal_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:52:19.889442+00:00
-- url     : https://prove2.me/submissions/4d5518da-b8a3-496c-b18b-2fc0f570b4da

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralUniformizer_mem_upperIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralRoot_equation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralRoot_mem_upperIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Ideal.span
        ({quadraticArtinSchreierIntegralUniformizer P a ha} :
          Set (QuadraticArtinSchreierIntegralClosure P a ha)) ≤
      (quadraticArtinSchreierUpperIdeal P a ha) ^ 2 := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  let Q := quadraticArtinSchreierUpperIdeal P a ha
  let w := quadraticArtinSchreierIntegralRoot P a ha
  let t := quadraticArtinSchreierIntegralUniformizer P a ha
  have ht : t ∈ Q :=
    quadraticArtinSchreierIntegralUniformizer_mem_upperIdeal P a ha
  have hw : w ∈ Q := quadraticArtinSchreierIntegralRoot_mem_upperIdeal P a ha
  have hw2 : w ^ 2 ∈ Q ^ 2 := Ideal.pow_mem_pow hw 2
  have hterm : t * w ∈ Q ^ 2 := by
    have hmul : t * w ∈ Q * Q := Ideal.mul_mem_mul ht hw
    simpa only [pow_two] using hmul
  have hsum : w ^ 2 + t * w ∈ Q ^ 2 := (Q ^ 2).add_mem hw2 hterm
  have heq : w ^ 2 + t * w + t = 0 :=
    quadraticArtinSchreierIntegralRoot_equation P a ha
  have hteq : t = -(w ^ 2 + t * w) := by
    linear_combination heq
  change t ∈ Q ^ 2
  rw [hteq]
  exact (Q ^ 2).neg_mem hsum
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
