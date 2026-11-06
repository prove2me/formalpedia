-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStep_ramificationIdx_eq_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:53:54.534314+00:00
-- url     : https://prove2.me/submissions/aaed351a-57f4-4b96-ad32-4d4e5bb53ac9

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStep_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_map_maximalIdeal_eq_span_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_span_sourceStepIntegralUniformizer_le_upperIdeal_pow_sixteen
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
    (IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx'
      (sourceStepUpperIdeal P x hx) = 16 := by
  let O := P.valuationRing
  let C := SourceStepIntegralClosure P x hx
  let L := SourceStepField P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := sourceStepUpperIdeal P x hx
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  letI : Q.LiesOver m := sourceStepUpperIdeal_liesOver P x hx
  letI : Q.IsPrime := (sourceStepUpperIdeal_isMaximal P x hx).isPrime
  letI : NoZeroSMulDivisors O C := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap0 : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm0
  have hmap_le : Ideal.map (algebraMap O C) m ≤ Q ^ 16 := by
    simpa only [O, C, m, Q,
      map_maximalIdeal_eq_span_sourceStepIntegralUniformizer] using
      span_sourceStepIntegralUniformizer_le_upperIdeal_pow_sixteen P x hx
  have hmult : multiplicity Q (Q ^ 16) ≤
      multiplicity Q (Ideal.map (algebraMap O C) m) :=
    (sourceStepUpperHeightOne P x hx).multiplicity_le_of_ideal_ge hmap_le hmap0
  have hQprime : Prime Q :=
    Ideal.prime_of_isPrime (sourceStepUpperHeightOne P x hx).ne_bot inferInstance
  have hlower : 16 ≤ m.ramificationIdx' Q := by
    calc
      16 = multiplicity Q (Q ^ 16) := by
        symm
        exact multiplicity_pow_self_of_prime hQprime 16
      _ ≤ multiplicity Q (Ideal.map (algebraMap O C) m) := hmult
      _ = m.ramificationIdx' Q :=
        (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
          hmap0 (inferInstance : Q.IsPrime)).symm
  have hupper : m.ramificationIdx' Q ≤ Module.finrank K L :=
    Ideal.ramificationIdx_le_finrank C K L Q
  have hfinrank : Module.finrank K L = 16 := sourceStep_finrank P x hx
  change m.ramificationIdx' Q = 16
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
