-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryCoordinate_adjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:01:25.10602+00:00
-- url     : https://prove2.me/submissions/19ee0a9a-8388-4da3-9f9e-606c88c1e3e4

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
import Mathlib.FieldTheory.PrimitiveElement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AuxiliaryMinpoly
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepReciprocalRoot_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K]
variable [Algebra F256 K]
private theorem stepReciprocalRoot_eq_div_auxiliaryCoordinate
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepReciprocalRoot P x hx =
      stepFieldEmbedding P x hx x / stepAuxiliaryCoordinate P x hx := by
  have hx0 : stepFieldEmbedding P x hx x ≠ 0 := by
    have hxK : x ≠ 0 := by
      intro hzero
      subst x
      simp [GlobalPlace.order] at hx
    have hport := (stepFieldEmbedding P x hx).injective.ne hxK
    simp only [map_zero] at hport ⊢
    exact hport
  have hw0 := stepReciprocalRoot_ne_zero P x hx
  rw [stepAuxiliaryCoordinate]
  field_simp [hx0, hw0]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K]
variable [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    IntermediateField.adjoin K
        ({stepAuxiliaryCoordinate P x hx} : Set (StepField P x hx)) =
      (⊤ : IntermediateField K (StepField P x hx)) := by
  let w := stepReciprocalRoot P x hx
  let z := stepAuxiliaryCoordinate P x hx
  have hwAlgebraAdjoin : Algebra.adjoin K
      ({w} : Set (StepField P x hx)) = ⊤ := by
    have hport := (AdjoinRoot.powerBasis
      (stepPolynomial_monic P x hx).ne_zero).adjoin_gen_eq_top
    simp only [w, stepReciprocalRoot, AdjoinRoot.powerBasis_gen] at hport ⊢
    exact hport
  have hwAdjoin : IntermediateField.adjoin K
      ({w} : Set (StepField P x hx)) =
      (⊤ : IntermediateField K (StepField P x hx)) :=
    IntermediateField.adjoin_eq_top_of_algebra K
      ({w} : Set (StepField P x hx)) hwAlgebraAdjoin
  have hwMem : w ∈ IntermediateField.adjoin K
      ({z} : Set (StepField P x hx)) := by
    dsimp only [w, z]
    rw [stepReciprocalRoot_eq_div_auxiliaryCoordinate P x hx]
    exact div_mem (algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self K z)
  apply top_unique
  rw [← hwAdjoin]
  exact IntermediateField.adjoin_simple_le_iff.mpr hwMem
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
