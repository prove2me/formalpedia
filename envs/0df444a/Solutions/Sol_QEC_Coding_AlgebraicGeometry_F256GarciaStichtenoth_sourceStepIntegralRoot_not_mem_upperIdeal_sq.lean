-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepIntegralRoot_not_mem_upperIdeal_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:50:07.926815+00:00
-- url     : https://prove2.me/submissions/6a9a14f8-90bc-479e-879e-c0077ee05e52

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepIntegralUniformizer_mem_upperIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepIntegralRoot_equation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepIntegralRoot_mem_upperIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_map_maximalIdeal_eq_span_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_span_sourceStepIntegralUniformizer_le_upperIdeal_pow_sixteen
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStep_ramificationIdx_eq_sixteen
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    sourceStepIntegralRoot P x hx ∉ (sourceStepUpperIdeal P x hx) ^ 2 := by
  let O := P.valuationRing
  let C := SourceStepIntegralClosure P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := sourceStepUpperIdeal P x hx
  let w : C := sourceStepIntegralRoot P x hx
  let t : C := sourceStepIntegralUniformizer P x hx
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  intro hw2
  change w ∈ Q ^ 2 at hw2
  have ht : t ∈ Q := sourceStepIntegralUniformizer_mem_upperIdeal P x hx
  have hw : w ∈ Q := sourceStepIntegralRoot_mem_upperIdeal P x hx
  have ht16 : t ∈ Q ^ 16 := by
    exact span_sourceStepIntegralUniformizer_le_upperIdeal_pow_sixteen P x hx
      (Ideal.mem_span_singleton_self t)
  have hw15 : w ^ 15 ∈ Q ^ 15 := Ideal.pow_mem_pow hw 15
  have hw16_17 : w ^ 16 ∈ Q ^ 17 := by
    have hmul : w * w ^ 15 ∈ Q ^ 2 * Q ^ 15 :=
      Ideal.mul_mem_mul hw2 hw15
    rw [show w * w ^ 15 = w ^ 16 by ring,
      show Q ^ 2 * Q ^ 15 = Q ^ 17 by
        rw [show 17 = 2 + 15 by norm_num, pow_add]] at hmul
    exact hmul
  have hterm17 : t * w ^ 15 ∈ Q ^ 17 := by
    have hbase : t * w ∈ Q ^ 16 * Q := Ideal.mul_mem_mul ht16 hw
    have hQpow : Q ^ 16 * Q = Q ^ 17 := by
      simpa only [show 17 = 16 + 1 by norm_num] using (pow_succ Q 16).symm
    rw [hQpow] at hbase
    have hmul := (Q ^ 17).mul_mem_right (w ^ 14) hbase
    convert hmul using 1 <;> ring
  have hsum : w ^ 16 + t * w ^ 15 ∈ Q ^ 17 :=
    (Q ^ 17).add_mem hw16_17 hterm17
  have heq : w ^ 16 + t * w ^ 15 + t = 0 :=
    sourceStepIntegralRoot_equation P x hx
  have hteq : t = -(w ^ 16 + t * w ^ 15) := by
    linear_combination heq
  have ht17 : t ∈ Q ^ 17 := by
    rw [hteq]
    exact (Q ^ 17).neg_mem hsum
  have hmap17 : Ideal.map (algebraMap O C) m ≤ Q ^ 17 := by
    rw [show Ideal.map (algebraMap O C) m = Ideal.span ({t} : Set C) by
      simpa only [O, C, m, t] using
        map_maximalIdeal_eq_span_sourceStepIntegralUniformizer P x hx,
      Ideal.span_le, Set.singleton_subset_iff]
    exact ht17
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap0 : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm0
  have hmult17 : multiplicity Q (Q ^ 17) ≤
      multiplicity Q (Ideal.map (algebraMap O C) m) :=
    (sourceStepUpperHeightOne P x hx).multiplicity_le_of_ideal_ge hmap17 hmap0
  have hQprime : Prime Q := Ideal.prime_of_isPrime
    (sourceStepUpperHeightOne P x hx).ne_bot
    (sourceStepUpperIdeal_isMaximal P x hx).isPrime
  have hleft : multiplicity Q (Q ^ 17) = 17 :=
    multiplicity_pow_self_of_prime hQprime 17
  have hright : multiplicity Q (Ideal.map (algebraMap O C) m) = 16 := by
    rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
      hmap0 (sourceStepUpperIdeal_isMaximal P x hx).isPrime]
    exact sourceStep_ramificationIdx_eq_sixteen P x hx
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
