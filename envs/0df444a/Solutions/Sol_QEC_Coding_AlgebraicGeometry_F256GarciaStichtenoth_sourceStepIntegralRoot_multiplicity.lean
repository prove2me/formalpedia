-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepIntegralRoot_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:51:31.448941+00:00
-- url     : https://prove2.me/submissions/5efac3aa-6a60-4176-9272-a116c8787429

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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepIntegralRoot_mem_upperIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepIntegralRoot_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepIntegralRoot_not_mem_upperIdeal_sq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
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
      (Ideal.span ({sourceStepIntegralRoot P x hx} :
        Set (SourceStepIntegralClosure P x hx))) = 1 := by
  let C := SourceStepIntegralClosure P x hx
  let Q : Ideal C := sourceStepUpperIdeal P x hx
  let w : C := sourceStepIntegralRoot P x hx
  let I : Ideal C := Ideal.span ({w} : Set C)
  have hI0 : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    simpa only [w] using sourceStepIntegralRoot_ne_zero P x hx
  have hle : Ideal.map (algebraMap C C) I ≤ Q ^ 1 := by
    rw [Algebra.algebraMap_self, Ideal.map_id, pow_one]
    exact Ideal.span_le.2 (Set.singleton_subset_iff.2
      (sourceStepIntegralRoot_mem_upperIdeal P x hx))
  have hnle : ¬Ideal.map (algebraMap C C) I ≤ Q ^ (1 + 1) := by
    rw [Algebra.algebraMap_self, Ideal.map_id, one_add_one_eq_two]
    intro h
    exact sourceStepIntegralRoot_not_mem_upperIdeal_sq P x hx
      (h (Ideal.mem_span_singleton_self w))
  have hram : I.ramificationIdx' Q = 1 := Ideal.ramificationIdx_spec hle hnle
  have hmap0 : Ideal.map (algebraMap C C) I ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hI0
  calc
    multiplicity Q I = multiplicity Q (Ideal.map (algebraMap C C) I) := by
      rw [Algebra.algebraMap_self, Ideal.map_id]
    _ = I.ramificationIdx' Q :=
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hmap0
        (sourceStepUpperIdeal_isMaximal P x hx).isPrime).symm
    _ = 1 := hram
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
