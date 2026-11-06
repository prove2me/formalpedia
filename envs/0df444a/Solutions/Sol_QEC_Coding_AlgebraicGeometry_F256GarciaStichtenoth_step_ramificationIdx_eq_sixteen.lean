-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.step_ramificationIdx_eq_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:00:35.621605+00:00
-- url     : https://prove2.me/submissions/fbf51d8c-3a27-4b89-9bbb-2f0cd801aaf7

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.GoingUp
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_map_maximalIdeal_eq_span_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_span_stepIntegralUniformizer_le_upperIdeal_pow_sixteen
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepField_finrank
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
    (IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx'
      (stepUpperIdeal P x hx) = 16 := by
  let O := P.valuationRing
  let C := StepIntegralClosure P x hx
  let L := StepField P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := stepUpperIdeal P x hx
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  letI : Q.LiesOver m := stepUpperIdeal_liesOver P x hx
  letI : Q.IsPrime := (stepUpperIdeal_isMaximal P x hx).isPrime
  letI : NoZeroSMulDivisors O C :=
    ⟨fun {_ _} h => (smul_eq_zero.mp h)⟩
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap0 : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm0
  have hmap_le : Ideal.map (algebraMap O C) m ≤ Q ^ 16 := by
    simpa only [O, C, m, Q,
      map_maximalIdeal_eq_span_stepIntegralUniformizer] using
      span_stepIntegralUniformizer_le_upperIdeal_pow_sixteen P x hx
  have hmult : multiplicity Q (Q ^ 16) ≤
      multiplicity Q (Ideal.map (algebraMap O C) m) :=
    (stepUpperHeightOne P x hx).multiplicity_le_of_ideal_ge hmap_le hmap0
  have hQprime : Prime Q :=
    Ideal.prime_of_isPrime (stepUpperHeightOne P x hx).ne_bot inferInstance
  have hlower : 16 ≤ m.ramificationIdx' Q := by
    calc
      16 = multiplicity Q (Q ^ 16) := by
        symm
        exact multiplicity_pow_self_of_prime hQprime 16
      _ ≤ multiplicity Q (Ideal.map (algebraMap O C) m) := hmult
      _ = m.ramificationIdx' Q :=
        (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
          hmap0 (inferInstance : Q.IsPrime)).symm
  have hupper : m.ramificationIdx' Q ≤ Module.finrank K L := by
    exact Ideal.ramificationIdx_le_finrank C K L Q
  have hfinrank : Module.finrank K L = 16 :=
    stepField_finrank P x hx
  change m.ramificationIdx' Q = 16
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
