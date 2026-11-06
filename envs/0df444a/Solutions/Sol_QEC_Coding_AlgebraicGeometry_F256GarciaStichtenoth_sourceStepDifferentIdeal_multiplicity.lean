-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepDifferentIdeal_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:31:02.396556+00:00
-- url     : https://prove2.me/submissions/74930107-d0dd-40e6-a3ea-0e8f68243737

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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_map_maximalIdeal_eq_span_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStep_ramificationIdx_eq_sixteen
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepIntegralRoot_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepIntegralRoot_multiplicity
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepDifferentIdeal_eq_span
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
    multiplicity (sourceStepUpperIdeal P x hx)
        (differentIdeal P.valuationRing
          (SourceStepIntegralClosure P x hx)) = 30 := by
  let O := P.valuationRing
  let C := SourceStepIntegralClosure P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := sourceStepUpperIdeal P x hx
  let t : C := sourceStepIntegralUniformizer P x hx
  let w : C := sourceStepIntegralRoot P x hx
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  have hm_ne_bot : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap_ne_bot : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm_ne_bot
  have hmap : Ideal.map (algebraMap O C) m =
      Ideal.span ({t} : Set C) := by
    simpa only [O, C, m, t] using
      map_maximalIdeal_eq_span_sourceStepIntegralUniformizer P x hx
  have hQ_prime : Prime Q := Ideal.prime_of_isPrime
    (sourceStepUpperHeightOne P x hx).ne_bot
    (sourceStepUpperHeightOne P x hx).isPrime
  have ht_ne_bot : Ideal.span ({t} : Set C) ≠ ⊥ := by
    rw [← hmap]
    exact hmap_ne_bot
  have hw_ne_bot : Ideal.span ({w} : Set C) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    simpa only [w] using sourceStepIntegralRoot_ne_zero P x hx
  have ht_finite : FiniteMultiplicity Q (Ideal.span ({t} : Set C)) :=
    FiniteMultiplicity.of_prime_left hQ_prime ht_ne_bot
  have hw_finite : FiniteMultiplicity Q (Ideal.span ({w} : Set C)) :=
    FiniteMultiplicity.of_prime_left hQ_prime hw_ne_bot
  have hproduct_finite : FiniteMultiplicity Q
      (Ideal.span ({t} : Set C) * (Ideal.span ({w} : Set C)) ^ 14) :=
    hQ_prime.finiteMultiplicity_mul ht_finite (hw_finite.pow hQ_prime)
  have ht_multiplicity : multiplicity Q (Ideal.span ({t} : Set C)) = 16 := by
    calc
      multiplicity Q (Ideal.span ({t} : Set C)) =
          multiplicity Q (Ideal.map (algebraMap O C) m) := by rw [hmap]
      _ = m.ramificationIdx' Q :=
        (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
          hmap_ne_bot (sourceStepUpperHeightOne P x hx).isPrime).symm
      _ = 16 := by
        simpa only [O, C, m, Q] using
          sourceStep_ramificationIdx_eq_sixteen P x hx
  have hw_multiplicity : multiplicity Q (Ideal.span ({w} : Set C)) = 1 := by
    simpa only [C, Q, w] using sourceStepIntegralRoot_multiplicity P x hx
  have hdifferent : differentIdeal O C =
      Ideal.span ({t} : Set C) * (Ideal.span ({w} : Set C)) ^ 14 := by
    calc
      differentIdeal O C = Ideal.span ({t * w ^ 14} : Set C) := by
        simpa only [O, C, t, w] using sourceStepDifferentIdeal_eq_span P x hx
      _ = Ideal.span ({t} : Set C) * Ideal.span ({w ^ 14} : Set C) :=
        (Ideal.span_singleton_mul_span_singleton t (w ^ 14)).symm
      _ = Ideal.span ({t} : Set C) * (Ideal.span ({w} : Set C)) ^ 14 := by
        rw [Ideal.span_singleton_pow]
  change multiplicity Q (differentIdeal O C) = 30
  rw [hdifferent, multiplicity_mul hQ_prime hproduct_finite,
    hw_finite.multiplicity_pow hQ_prime,
    ht_multiplicity, hw_multiplicity]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
