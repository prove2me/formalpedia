-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierDifferentIdeal_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:53:37.397492+00:00
-- url     : https://prove2.me/submissions/21eb9b0b-0838-4419-b78a-af7f526cc045

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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreier_ramificationIdx_eq_two
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierDifferentIdeal_eq_span
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
    multiplicity (quadraticArtinSchreierUpperIdeal P a ha)
        (differentIdeal P.valuationRing
          (QuadraticArtinSchreierIntegralClosure P a ha)) = 2 := by
  let O := P.valuationRing
  let C := QuadraticArtinSchreierIntegralClosure P a ha
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q : Ideal C := quadraticArtinSchreierUpperIdeal P a ha
  let t : C := quadraticArtinSchreierIntegralUniformizer P a ha
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  have hm_ne_bot : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap_ne_bot : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm_ne_bot
  have hmap : Ideal.map (algebraMap O C) m =
      Ideal.span ({t} : Set C) := by
    simpa only [O, C, m, t] using
      map_maximalIdeal_eq_span_quadraticArtinSchreierIntegralUniformizer
        P a ha
  rw [quadraticArtinSchreierDifferentIdeal_eq_span]
  calc
    multiplicity Q (Ideal.span ({t} : Set C)) =
        multiplicity Q (Ideal.map (algebraMap O C) m) := by rw [hmap]
    _ = m.ramificationIdx' Q :=
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
        hmap_ne_bot
        (quadraticArtinSchreierUpperIdeal_isMaximal P a ha).isPrime).symm
    _ = 2 := quadraticArtinSchreier_ramificationIdx_eq_two P a ha
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
