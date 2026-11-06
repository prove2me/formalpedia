-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.rationalPlace_order_X_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:16:28.338416+00:00
-- url     : https://prove2.me/submissions/ba6839c2-f3e3-4092-8c3e-618448fbe76b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalRecursionOrders
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepDistinguishedCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepFieldEmbedding
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepReciprocalRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_comapAlgEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepDistinguishedCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepFieldEmbedding
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepReciprocalRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.comapAlgEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
open IntermediateField
open scoped Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
section SourceBasicRationalPlaces
open scoped BigOperators
attribute [local instance] sourceBasicRationalF256CharTwo
private theorem sourceBasicRationalPlace_order_X_of_pole
    {k : Type*} [_root_.Field k] [Finite k]
    (P : GlobalPlace k (RatFunc k))
    (hX : 1 < P.valuation RatFunc.X) :
    P.order RatFunc.X = -1 := by
  classical
  have hXne : P.valuation RatFunc.X ≠ 0 :=
    P.valuation.ne_zero_iff.mpr RatFunc.X_ne_zero
  have hmultiple : ∀ f : RatFunc k, f ≠ 0 →
      ∃ n : ℤ, P.order f = n * P.order RatFunc.X := by
    intro f
    induction f using RatFunc.induction_on with
    | f p q hq =>
      intro hf
      have hp : p ≠ 0 := by
        intro hp
        subst p
        simp at hf
      refine ⟨(p.natDegree : ℤ) - (q.natDegree : ℤ), ?_⟩
      unfold GlobalPlace.order
      rw [map_div₀, ← RatFunc.coePolynomial_eq_algebraMap,
        ← RatFunc.coePolynomial_eq_algebraMap,
        Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          k (v := P.valuation) hX hp,
        Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
          k (v := P.valuation) hX hq,
        WithZero.log_div (pow_ne_zero _ hXne) (pow_ne_zero _ hXne)]
      simp only [WithZero.log_pow, nsmul_eq_mul]
      ring
  have hu : P.uniformizer ≠ 0 := by
    apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  obtain ⟨n, hn⟩ := hmultiple P.uniformizer hu
  rw [P.order_uniformizer] at hn
  have hunit : P.order RatFunc.X = 1 ∨ P.order RatFunc.X = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one (by
      simpa only [mul_comm] using hn.symm)
  have hpositive : 0 < WithZero.log (P.valuation RatFunc.X) := by
    simpa only [WithZero.log_one] using
      (WithZero.log_lt_log one_ne_zero hXne).mpr hX
  unfold GlobalPlace.order at hunit ⊢
  omega
end SourceBasicRationalPlaces
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open IntermediateField
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open scoped BigOperators
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicRationalF256CharTwo
attribute [local instance] sourceBasicRationalF256CharTwo
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    {k : Type*} [_root_.Field k] [Finite k]
    (P : GlobalPlace k (RatFunc k)) :
    P.order RatFunc.X = -1 ∨ 0 ≤ P.order RatFunc.X := by
  by_cases hX : P.valuation RatFunc.X ≤ 1
  · exact Or.inr ((P.regularAt_iff_order_nonnegative RatFunc.X_ne_zero).mp hX)
  · exact Or.inl (sourceBasicRationalPlace_order_X_of_pole P (lt_of_not_ge hX))
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
