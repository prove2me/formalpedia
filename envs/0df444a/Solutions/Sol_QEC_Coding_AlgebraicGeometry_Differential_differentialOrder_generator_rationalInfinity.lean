-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.differentialOrder_generator_rationalInfinity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:46:20.108898+00:00
-- url     : https://prove2.me/submissions/03cd9134-796a-4ce3-b10e-5d74ca15f113

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinitySimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_logarithmicDifferential_isGlobalSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_localDifferentialLattice_iff_differentialOrder_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_logarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differential_eq_functionFieldDerivation_smul_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalBaseInfinityCancellation_rationalInfinity_order_eq_neg_intDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
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
open scoped Polynomial RatFunc WithZero
namespace QEC.Coding.AlgebraicGeometry
namespace Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
private theorem rationalInfinity_order_inverseX :
    (GlobalPlace.rationalInfinity k).order (RatFunc.X : RatFunc k)⁻¹ = 1 := by
  rw [GlobalPlace.order_inv,
    RationalBaseInfinityCancellation.rationalInfinity_order_eq_neg_intDegree
      k RatFunc.X RatFunc.X_ne_zero,
    RatFunc.intDegree_X]
  norm_num
private theorem differentialOrder_logarithmic_eq_neg_one_of_order_eq_one
    (P : GlobalPlace k (RatFunc k)) (f : RatFunc k) (hf : f ≠ 0)
    (horder : P.order f = 1) :
    differentialOrder (k := k) (F := RatFunc k) P
        (logarithmicDifferential (k := k) (F := RatFunc k) f)
        (logarithmicDifferential_ne_zero_of_order_eq_one P f hf horder) = -1 := by
  let omega := logarithmicDifferential (k := k) (F := RatFunc k) f
  let homega : omega ≠ 0 :=
    logarithmicDifferential_ne_zero_of_order_eq_one P f hf horder
  have hsimple : omega ∈ simplePoleDifferentialLattice P :=
    logarithmicDifferential_isGlobalSimplePole
      (k := k) (F := RatFunc k) f hf P
  have hresidue :
      simplePoleResidue (k := k) (F := RatFunc k) P
          (logarithmicDifferentialAtSimplePole
            (k := k) (F := RatFunc k) P f hf) = 1 := by
    simpa only [horder, Int.cast_one] using
      (simplePoleResidue_logarithmicDifferential
        (k := k) (F := RatFunc k) P f hf)
  have hnotRegular : omega ∉ localDifferentialLattice P := by
    intro hregular
    have hzero := simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
      (k := k) (F := RatFunc k) P
      (logarithmicDifferentialAtSimplePole
        (k := k) (F := RatFunc k) P f hf) hregular
    rw [hresidue] at hzero
    exact one_ne_zero hzero
  have hge : -1 ≤ differentialOrder (k := k) (F := RatFunc k) P omega homega :=
    (mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
      (k := k) (F := RatFunc k) P omega homega).mp hsimple
  have hnge : ¬ 0 ≤ differentialOrder (k := k) (F := RatFunc k) P omega homega := by
    intro hnonnegative
    apply hnotRegular
    exact (mem_localDifferentialLattice_iff_differentialOrder_nonnegative
      (k := k) (F := RatFunc k) P omega homega).mpr hnonnegative
  apply le_antisymm
  · exact Int.le_sub_one_iff.mpr (lt_of_not_ge hnge)
  · exact hge
end Differential
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution :
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k)
        (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k)) = -2 := by
  let y : RatFunc k := (RatFunc.X : RatFunc k)⁻¹
  let c : RatFunc k := -(RatFunc.X : RatFunc k)⁻¹
  have hy : y ≠ 0 := inv_ne_zero RatFunc.X_ne_zero
  have hc : c ≠ 0 := neg_ne_zero.mpr hy
  have hyOrder : (GlobalPlace.rationalInfinity k).order y = 1 :=
    rationalInfinity_order_inverseX
  have hminusOneOrder :
      (GlobalPlace.rationalInfinity k).order (-1 : RatFunc k) = 0 := by
    simpa using (GlobalPlace.rationalInfinity k).order_algebraMap
      (-1 : k) (by simp)
  have hcOrder : (GlobalPlace.rationalInfinity k).order c = 1 := by
    rw [show c = (-1 : RatFunc k) * y by simp [c, y]]
    rw [GlobalPlace.order_mul (GlobalPlace.rationalInfinity k)
      (by simp) hy, hminusOneOrder, hyOrder]
    norm_num
  have hlogEq : logarithmicDifferential (k := k) (F := RatFunc k) y =
      c • functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
    have hDX :
        functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X = 1 := by
      simpa using
        (functionFieldDerivation_apply_X (k := k) (F := RatFunc k))
    rw [logarithmicDifferential,
      differential_eq_functionFieldDerivation_smul_generator,
      Derivation.leibniz_inv, hDX]
    simp only [smul_smul, smul_eq_mul, y, c]
    field_simp [RatFunc.X_ne_zero]
  have hlogOrder := differentialOrder_logarithmic_eq_neg_one_of_order_eq_one
    (GlobalPlace.rationalInfinity k) y hy hyOrder
  have hscaledOrder :
      differentialOrder (k := k) (F := RatFunc k)
          (GlobalPlace.rationalInfinity k)
          (c • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
          (smul_ne_zero hc
            (functionFieldDifferentialGenerator_ne_zero
              (k := k) (F := RatFunc k))) = -1 := by
    simpa only [hlogEq] using hlogOrder
  rw [differentialOrder_smul (k := k) (F := RatFunc k)
    (GlobalPlace.rationalInfinity k) c hc
    (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
    (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k)),
    hcOrder] at hscaledOrder
  omega
end QEC.Coding.AlgebraicGeometry.Differential
