-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreier_ramificationIdx_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:53:29.891309+00:00
-- url     : https://prove2.me/submissions/33970c5f-8b20-40b5-9d21-9168bef1d195

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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_map_maximalIdeal_eq_span_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_span_quadraticArtinSchreierIntegralUniformizer_le_upperIdeal_sq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreier_finrank
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
    (IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx'
      (quadraticArtinSchreierUpperIdeal P a ha) = 2 := by
  let O := P.valuationRing
  let C := QuadraticArtinSchreierIntegralClosure P a ha
  let L := QuadraticArtinSchreierField P a ha
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := quadraticArtinSchreierUpperIdeal P a ha
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  letI : Q.LiesOver m := quadraticArtinSchreierUpperIdeal_liesOver P a ha
  letI : Q.IsPrime :=
    (quadraticArtinSchreierUpperIdeal_isMaximal P a ha).isPrime
  letI : NoZeroSMulDivisors O C := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap0 : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm0
  have hmap_le : Ideal.map (algebraMap O C) m ≤ Q ^ 2 := by
    rw [show Ideal.map (algebraMap O C) m = Ideal.span
      ({quadraticArtinSchreierIntegralUniformizer P a ha} : Set C) by
        simpa only [O, C, m] using
          map_maximalIdeal_eq_span_quadraticArtinSchreierIntegralUniformizer
            P a ha]
    exact span_quadraticArtinSchreierIntegralUniformizer_le_upperIdeal_sq P a ha
  have hmult : multiplicity Q (Q ^ 2) ≤
      multiplicity Q (Ideal.map (algebraMap O C) m) :=
    (quadraticArtinSchreierUpperHeightOne P a ha).multiplicity_le_of_ideal_ge
      hmap_le hmap0
  have hQprime : Prime Q :=
    Ideal.prime_of_isPrime
      (quadraticArtinSchreierUpperHeightOne P a ha).ne_bot inferInstance
  have hlower : 2 ≤ m.ramificationIdx' Q := by
    calc
      2 = multiplicity Q (Q ^ 2) := by
        symm
        exact multiplicity_pow_self_of_prime hQprime 2
      _ ≤ multiplicity Q (Ideal.map (algebraMap O C) m) := hmult
      _ = m.ramificationIdx' Q :=
        (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
          hmap0 (inferInstance : Q.IsPrime)).symm
  have hupper : m.ramificationIdx' Q ≤ Module.finrank K L :=
    Ideal.ramificationIdx_le_finrank C K L Q
  have hfinrank : Module.finrank K L = 2 :=
    quadraticArtinSchreier_finrank P a ha
  change m.ramificationIdx' Q = 2
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
