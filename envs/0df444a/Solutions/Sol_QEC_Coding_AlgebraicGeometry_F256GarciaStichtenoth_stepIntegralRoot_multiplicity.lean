-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepIntegralRoot_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:03:01.133077+00:00
-- url     : https://prove2.me/submissions/77af0d08-95ed-41be-835a-17bfcfd3ee23

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.GoingUp
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepIntegralRoot_mem_upperIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepIntegralRoot_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepIntegralRoot_not_mem_upperIdeal_sq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
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
    multiplicity (stepUpperIdeal P x hx)
      (Ideal.span ({stepIntegralRoot P x hx} :
        Set (StepIntegralClosure P x hx))) = 1 := by
  let C := StepIntegralClosure P x hx
  let Q : Ideal C := stepUpperIdeal P x hx
  let w : C := stepIntegralRoot P x hx
  let I : Ideal C := Ideal.span ({w} : Set C)
  have hI0 : I ≠ ⊥ := by
    change Ideal.span ({w} : Set C) ≠ ⊥
    rw [Ne, Ideal.span_singleton_eq_bot]
    simpa only [w] using stepIntegralRoot_ne_zero P x hx
  have hle : Ideal.map (algebraMap C C) I ≤ Q ^ 1 := by
    rw [Algebra.algebraMap_self, Ideal.map_id, pow_one]
    change Ideal.span ({w} : Set C) ≤ Q
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact stepIntegralRoot_mem_upperIdeal P x hx
  have hnle : ¬Ideal.map (algebraMap C C) I ≤ Q ^ (1 + 1) := by
    rw [Algebra.algebraMap_self, Ideal.map_id, one_add_one_eq_two]
    change ¬Ideal.span ({w} : Set C) ≤ Q ^ 2
    intro h
    exact stepIntegralRoot_not_mem_upperIdeal_sq P x hx
      (h (Ideal.mem_span_singleton_self w))
  have hram : I.ramificationIdx' Q = 1 :=
    Ideal.ramificationIdx_spec hle hnle
  have hmap0 : Ideal.map (algebraMap C C) I ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hI0
  calc
    multiplicity Q I = multiplicity Q (Ideal.map (algebraMap C C) I) := by
      rw [Algebra.algebraMap_self, Ideal.map_id]
    _ = I.ramificationIdx' Q :=
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hmap0
        (stepUpperIdeal_isMaximal P x hx).isPrime).symm
    _ = 1 := hram
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
