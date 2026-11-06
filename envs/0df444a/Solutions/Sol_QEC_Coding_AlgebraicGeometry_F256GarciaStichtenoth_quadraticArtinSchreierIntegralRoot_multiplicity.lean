-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierIntegralRoot_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:50:57.117423+00:00
-- url     : https://prove2.me/submissions/da2e079e-e794-4207-bbba-d22ee83086d7

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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralRoot_mem_upperIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralRoot_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralRoot_not_mem_upperIdeal_sq
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
    multiplicity (quadraticArtinSchreierUpperIdeal P a ha)
      (Ideal.span
        ({quadraticArtinSchreierIntegralRoot P a ha} :
          Set (QuadraticArtinSchreierIntegralClosure P a ha))) = 1 := by
  let C := QuadraticArtinSchreierIntegralClosure P a ha
  let Q : Ideal C := quadraticArtinSchreierUpperIdeal P a ha
  let w : C := quadraticArtinSchreierIntegralRoot P a ha
  let I : Ideal C := Ideal.span ({w} : Set C)
  have hI0 : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    simpa only [w] using quadraticArtinSchreierIntegralRoot_ne_zero P a ha
  have hle : Ideal.map (algebraMap C C) I ≤ Q ^ 1 := by
    rw [Algebra.algebraMap_self, Ideal.map_id, pow_one]
    exact Ideal.span_le.2 (Set.singleton_subset_iff.2
      (quadraticArtinSchreierIntegralRoot_mem_upperIdeal P a ha))
  have hnle : ¬Ideal.map (algebraMap C C) I ≤ Q ^ (1 + 1) := by
    rw [Algebra.algebraMap_self, Ideal.map_id, one_add_one_eq_two]
    intro h
    exact quadraticArtinSchreierIntegralRoot_not_mem_upperIdeal_sq P a ha
      (h (Ideal.mem_span_singleton_self w))
  have hram : I.ramificationIdx' Q = 1 := Ideal.ramificationIdx_spec hle hnle
  have hmap0 : Ideal.map (algebraMap C C) I ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hI0
  calc
    multiplicity Q I = multiplicity Q (Ideal.map (algebraMap C C) I) := by
      rw [Algebra.algebraMap_self, Ideal.map_id]
    _ = I.ramificationIdx' Q :=
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hmap0
        (quadraticArtinSchreierUpperIdeal_isMaximal P a ha).isPrime).symm
    _ = 1 := hram
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
