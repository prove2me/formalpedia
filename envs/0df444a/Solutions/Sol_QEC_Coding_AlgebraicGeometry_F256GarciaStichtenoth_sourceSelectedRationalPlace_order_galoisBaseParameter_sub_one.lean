-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRationalPlace_order_galoisBaseParameter_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:50:47.638417+00:00
-- url     : https://prove2.me/submissions/4b83adda-d90b-429a-ace0-debf2e42df54

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaceOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisBaseParameter_sub_one_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_baseRationalPlace_order_algebraMap_polynomial
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_galoisBaseZValue_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_galoisBaseZValue_eq_one_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSelectedRationalPlace_coordinate_split
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSelectedRationalPlace_succ
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitAbovePlace_order_sourceStepEmbedding
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
private theorem sourceSelectedSplitPolynomial_derivative :
    sourceSelectedSplitPolynomial.derivative =
      (Polynomial.X ^ 16 + Polynomial.X) ^ 14 := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  rw [sourceSelectedSplitPolynomial, Polynomial.derivative_sub,
    Polynomial.derivative_pow, Polynomial.derivative_add,
    Polynomial.derivative_X_pow, Polynomial.derivative_X,
    Polynomial.derivative_one]
  reduce_mod_char!
  simp
private theorem sourceSelectedSplitPolynomial_ne_zero :
    sourceSelectedSplitPolynomial ≠ 0 := by
  intro hzero
  have hderivative := congrArg Polynomial.derivative hzero
  rw [sourceSelectedSplitPolynomial_derivative, map_zero] at hderivative
  exact (pow_ne_zero 14
    (Polynomial.monic_X_pow_add (by norm_num)).ne_zero) hderivative
private theorem sourceSelectedSplitPolynomial_isRoot
    (a : GaloisBaseSplitPoint) :
    sourceSelectedSplitPolynomial.IsRoot (a : F256) := by
  rw [Polynomial.IsRoot, sourceSelectedSplitPolynomial]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  have hz := (galoisBaseZValue_eq_one_iff (a : F256)).2 a.property
  simpa only [galoisBaseZValue_eq, sub_eq_zero] using hz
private theorem sourceSelectedSplitPolynomial_derivative_eval_ne_zero
    (a : GaloisBaseSplitPoint) :
    sourceSelectedSplitPolynomial.derivative.eval (a : F256) ≠ 0 := by
  rw [sourceSelectedSplitPolynomial_derivative]
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
  apply pow_ne_zero
  simpa only [galoisBaseWValue_eq] using a.property
private theorem sourceSelectedSplitPolynomial_rootMultiplicity
    (a : GaloisBaseSplitPoint) :
    sourceSelectedSplitPolynomial.rootMultiplicity (a : F256) = 1 := by
  have hpositive : 0 <
      sourceSelectedSplitPolynomial.rootMultiplicity (a : F256) :=
    (Polynomial.rootMultiplicity_pos
      sourceSelectedSplitPolynomial_ne_zero).2
      (sourceSelectedSplitPolynomial_isRoot a)
  have hnotGreater : ¬ 1 <
      sourceSelectedSplitPolynomial.rootMultiplicity (a : F256) := by
    intro hgreater
    have hroot := (Polynomial.one_lt_rootMultiplicity_iff_isRoot
      sourceSelectedSplitPolynomial_ne_zero).1 hgreater
    exact sourceSelectedSplitPolynomial_derivative_eval_ne_zero a hroot.2
  omega
private theorem sourceGaloisBaseParameter_sub_one_eq_polynomial (m : ℕ) :
    sourceGaloisBaseParameter m - 1 =
      algebraMap (RatFunc F256) (SourceField m)
        (algebraMap (Polynomial F256) (RatFunc F256)
          sourceSelectedSplitPolynomial) := by
  rw [sourceGaloisBaseParameter]
  calc
    algebraMap (RatFunc F256) (SourceField m) galoisBaseZ - 1 =
        algebraMap (RatFunc F256) (SourceField m) (galoisBaseZ - 1) := by
      rw [map_sub, map_one]
    _ = algebraMap (RatFunc F256) (SourceField m)
        (algebraMap (Polynomial F256) (RatFunc F256)
          sourceSelectedSplitPolynomial) := by
      congr 1
      simp [sourceSelectedSplitPolynomial, galoisBaseZ, galoisBaseW,
        RatFunc.algebraMap_X]
private theorem sourceGaloisBaseParameter_succ (m : ℕ) :
    sourceGaloisBaseParameter (m + 1) =
      sourceRecursionEmbedding m (sourceGaloisBaseParameter m) := by
  rfl
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution :
    ∀ (m : ℕ) (index : SourceSelectedPlaceIndex m),
      (sourceSelectedRationalPlace m index).place.order
          (sourceGaloisBaseParameter m - 1) = 1
  | 0, a => by
      let b : BasePoint := Units.mk0 (a : F256) (by
        intro ha
        apply a.property
        simp [galoisBaseWValue_eq, ha])
      have horder := baseRationalPlace_order_algebraMap_polynomial b
        sourceSelectedSplitPolynomial sourceSelectedSplitPolynomial_ne_zero
      have hb : (b : F256) = (a : F256) := rfl
      rw [hb, sourceSelectedSplitPolynomial_rootMultiplicity] at horder
      rw [sourceSelectedRationalPlace_zero,
        sourceGaloisBaseParameter_sub_one_eq_polynomial]
      simp only [b] at horder ⊢
      exact horder
  | m + 1, index => by
      rcases index with ⟨index, c⟩
      have htransport := sourceSplitAbovePlace_order_sourceStepEmbedding
        (sourceSelectedRationalPlace m index)
        (sourceDistinguishedPlace m) (sourceDistinguishedCoordinate m)
        (sourceDistinguishedCoordinate_order m)
        (sourceSelectedRationalPlace_coordinate_regular m index)
        (sourceSelectedRationalPlace_coordinate_split m index) c
        (sourceGaloisBaseParameter m - 1)
        (sourceGaloisBaseParameter_sub_one_ne_zero m)
      have hlower :=
        solution m index
      rw [← hlower]
      simp only [sourceSelectedRationalPlace_succ,
        sourceGaloisBaseParameter_succ, map_sub, map_one,
        RationalPlace.place] at htransport ⊢
      exact htransport
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
