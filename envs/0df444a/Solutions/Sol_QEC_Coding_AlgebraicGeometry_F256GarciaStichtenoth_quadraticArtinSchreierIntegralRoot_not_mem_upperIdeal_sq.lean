-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierIntegralRoot_not_mem_upperIdeal_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:49:26.618048+00:00
-- url     : https://prove2.me/submissions/f02a0a3e-8123-4dab-931d-dce7848ed2b7

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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralRoot_equation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralRoot_mem_upperIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_map_maximalIdeal_eq_span_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_span_quadraticArtinSchreierIntegralUniformizer_le_upperIdeal_sq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreier_ramificationIdx_eq_two
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
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
    quadraticArtinSchreierIntegralRoot P a ha ∉
      (quadraticArtinSchreierUpperIdeal P a ha) ^ 2 := by
  let O := P.valuationRing
  let C := QuadraticArtinSchreierIntegralClosure P a ha
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := quadraticArtinSchreierUpperIdeal P a ha
  let w : C := quadraticArtinSchreierIntegralRoot P a ha
  let t : C := quadraticArtinSchreierIntegralUniformizer P a ha
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  intro hw2
  change w ∈ Q ^ 2 at hw2
  have ht2 : t ∈ Q ^ 2 :=
    span_quadraticArtinSchreierIntegralUniformizer_le_upperIdeal_sq P a ha
      (Ideal.mem_span_singleton_self t)
  have hw : w ∈ Q := quadraticArtinSchreierIntegralRoot_mem_upperIdeal P a ha
  have hw3 : w ^ 2 ∈ Q ^ 3 := by
    have hmul : w * w ∈ Q ^ 2 * Q := Ideal.mul_mem_mul hw2 hw
    rw [show w * w = w ^ 2 by ring,
      show Q ^ 2 * Q = Q ^ 3 by
        rw [show 3 = 2 + 1 by norm_num, pow_add, pow_one]] at hmul
    exact hmul
  have hterm3 : t * w ∈ Q ^ 3 := by
    have hmul : t * w ∈ Q ^ 2 * Q := Ideal.mul_mem_mul ht2 hw
    rw [show Q ^ 2 * Q = Q ^ 3 by
      rw [show 3 = 2 + 1 by norm_num, pow_add, pow_one]] at hmul
    exact hmul
  have hsum : w ^ 2 + t * w ∈ Q ^ 3 :=
    (Q ^ 3).add_mem hw3 hterm3
  have heq : w ^ 2 + t * w + t = 0 :=
    quadraticArtinSchreierIntegralRoot_equation P a ha
  have hteq : t = -(w ^ 2 + t * w) := by
    linear_combination heq
  have ht3 : t ∈ Q ^ 3 := by
    rw [hteq]
    exact (Q ^ 3).neg_mem hsum
  have hmap3 : Ideal.map (algebraMap O C) m ≤ Q ^ 3 := by
    rw [show Ideal.map (algebraMap O C) m = Ideal.span ({t} : Set C) by
      simpa only [O, C, m, t] using
        map_maximalIdeal_eq_span_quadraticArtinSchreierIntegralUniformizer
          P a ha,
      Ideal.span_le, Set.singleton_subset_iff]
    exact ht3
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap0 : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm0
  have hmult3 : multiplicity Q (Q ^ 3) ≤
      multiplicity Q (Ideal.map (algebraMap O C) m) :=
    (quadraticArtinSchreierUpperHeightOne P a ha).multiplicity_le_of_ideal_ge
      hmap3 hmap0
  have hQprime : Prime Q := Ideal.prime_of_isPrime
    (quadraticArtinSchreierUpperHeightOne P a ha).ne_bot
    (quadraticArtinSchreierUpperIdeal_isMaximal P a ha).isPrime
  have hleft : multiplicity Q (Q ^ 3) = 3 :=
    multiplicity_pow_self_of_prime hQprime 3
  have hright : multiplicity Q (Ideal.map (algebraMap O C) m) = 2 := by
    rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
      hmap0 (quadraticArtinSchreierUpperIdeal_isMaximal P a ha).isPrime]
    exact quadraticArtinSchreier_ramificationIdx_eq_two P a ha
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
