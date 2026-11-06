-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepIntegralRoot_not_mem_upperIdeal_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:02:00.168644+00:00
-- url     : https://prove2.me/submissions/112ffeca-3fbd-49b8-a130-d76b0d7a9ef2

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.GoingUp
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepIntegralUniformizer_mem_upperIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepIntegralRoot_equation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepIntegralRoot_mem_upperIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_map_maximalIdeal_eq_span_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_step_ramificationIdx_eq_sixteen
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepIntegralRoot P x hx ∉ (stepUpperIdeal P x hx) ^ 2 := by
  let O := P.valuationRing
  let C := StepIntegralClosure P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := stepUpperIdeal P x hx
  let w : C := stepIntegralRoot P x hx
  let t : C := stepIntegralUniformizer P x hx
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  intro hw2
  change w ∈ Q ^ 2 at hw2
  have ht : t ∈ Q := stepIntegralUniformizer_mem_upperIdeal P x hx
  have hw : w ∈ Q := stepIntegralRoot_mem_upperIdeal P x hx
  have hw15 : w ^ 15 ∈ Q ^ 15 := Ideal.pow_mem_pow hw 15
  have hw16_17 : w ^ 16 ∈ Q ^ 17 := by
    have hmul : w * w ^ 15 ∈ Q ^ 2 * Q ^ 15 :=
      Ideal.mul_mem_mul hw2 hw15
    have hwpow : w * w ^ 15 = w ^ 16 := by
      ring
    have hQpow : Q ^ 2 * Q ^ 15 = Q ^ 17 := by
      rw [show 17 = 2 + 15 by norm_num, pow_add]
    rw [hwpow, hQpow] at hmul
    exact hmul
  have ht16 : t ^ 16 ∈ Q ^ 16 := Ideal.pow_mem_pow ht 16
  have hterm17 : t ^ 16 * w ^ 15 ∈ Q ^ 17 := by
    have hbase : t ^ 16 * w ∈ Q ^ 16 * Q :=
      Ideal.mul_mem_mul ht16 hw
    have hQpow : Q ^ 16 * Q = Q ^ 17 := by
      simpa only [show 17 = 16 + 1 by norm_num] using (pow_succ Q 16).symm
    rw [hQpow] at hbase
    have hmul := (Q ^ 17).mul_mem_right (w ^ 14) hbase
    convert hmul using 1 <;> ring
  have hsum : w ^ 16 + t ^ 16 * w ^ 15 ∈ Q ^ 17 :=
    (Q ^ 17).add_mem hw16_17 hterm17
  have heq : w ^ 16 + t ^ 16 * w ^ 15 + t = 0 :=
    stepIntegralRoot_equation P x hx
  have hteq : t = -(w ^ 16 + t ^ 16 * w ^ 15) := by
    linear_combination heq
  have ht17 : t ∈ Q ^ 17 := by
    rw [hteq]
    exact (Q ^ 17).neg_mem hsum
  have hspan17 : Ideal.span ({t} : Set C) ≤ Q ^ 17 := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ht17
  have hmap17 : Ideal.map (algebraMap O C) m ≤ Q ^ 17 := by
    simpa only [O, C, m, Q,
      map_maximalIdeal_eq_span_stepIntegralUniformizer] using hspan17
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap0 : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm0
  have hmult17 : multiplicity Q (Q ^ 17) ≤
      multiplicity Q (Ideal.map (algebraMap O C) m) :=
    (stepUpperHeightOne P x hx).multiplicity_le_of_ideal_ge hmap17 hmap0
  have hQprime : Prime Q := Ideal.prime_of_isPrime
    (stepUpperHeightOne P x hx).ne_bot
    (stepUpperIdeal_isMaximal P x hx).isPrime
  have hleft : multiplicity Q (Q ^ 17) = 17 :=
    multiplicity_pow_self_of_prime hQprime 17
  have hright : multiplicity Q (Ideal.map (algebraMap O C) m) = 16 := by
    rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
      hmap0 (stepUpperIdeal_isMaximal P x hx).isPrime]
    exact step_ramificationIdx_eq_sixteen P x hx
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
