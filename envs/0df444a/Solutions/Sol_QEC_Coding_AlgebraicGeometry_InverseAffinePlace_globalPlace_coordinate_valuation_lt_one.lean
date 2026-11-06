-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseAffinePlace.globalPlace_coordinate_valuation_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:14:39.445834+00:00
-- url     : https://prove2.me/submissions/4b3516d8-6974-4d3e-aeb8-1c4385b10e0d

import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_coordinate_mem_definingPrime
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_globalPlace_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_globalPlace_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_valuation_algebraMap_of_integral


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.InverseAffinePlace
open scoped Polynomial RatFunc
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
local notation3 "inverseRationalAlgebra" =>
  transportedRationalAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
local notation3 "inversePolynomialAlgebra" =>
  transportedPolynomialAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
local notation3 "inverseScalarTower" =>
  transportedScalarTower (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
local notation3 "inverseFunctionField" =>
  transportedFunctionField (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField)
local notation3 "inverseIsSeparable" =>
  transportedIsSeparable (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
local notation3 "inverseCarrier" =>
  carrier (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
namespace QEC.Coding.AlgebraicGeometry.InverseAffinePlace
theorem _root_.solution
    (v : infinityFibre (k := k) (F := F) (oldRationalAlgebra := oldRationalAlgebra)) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    letI : Algebra k F := AffinePlace.constantAlgebra k F
    (globalPlace (k := k) (F := F) (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable) v).valuation
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) < 1 := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  letI : Algebra k F := AffinePlace.constantAlgebra k F
  rw [@globalPlace_valuation k F _ _ _ oldPolynomialAlgebra oldRationalAlgebra oldScalarTower
    oldFunctionField oldSeparable v,
    @AffinePlace.valuation_algebraMap_of_integral k F _ _ _ inversePolynomialAlgebra inverseRationalAlgebra
      inverseScalarTower inverseFunctionField inverseIsSeparable]
  exact (v.1.intValuation_lt_one_iff_mem
    (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)).mpr
      (@coordinate_mem_definingPrime k F _ _ oldPolynomialAlgebra oldRationalAlgebra
        oldScalarTower oldFunctionField oldSeparable v)
end QEC.Coding.AlgebraicGeometry.InverseAffinePlace
