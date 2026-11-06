-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:34:50.923729+00:00
-- url     : https://prove2.me/submissions/6b48dc2c-ff3f-4d5a-a1cd-5a57894d7592

import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre

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
theorem _root_.solution :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    Nonempty (infinityFibre (k := k) (F := F) (oldRationalAlgebra := oldRationalAlgebra)) := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  letI : Module.IsTorsionFree k[X] F :=
    Module.IsTorsionFree.trans_faithfulSMul k[X] k⟮X⟯ F
  letI : Module.IsTorsionFree k[X] (_root_.FunctionField.ringOfIntegers k F) :=
    IsIntegralClosure.isTorsionFree k[X] F
  letI : Algebra.IsIntegral k[X] (_root_.FunctionField.ringOfIntegers k F) :=
    IsIntegralClosure.isIntegral_algebra k[X] F
  rcases (inferInstance : Nonempty
    ((infinityBasePrime k).primesOver (_root_.FunctionField.ringOfIntegers k F))) with ⟨P⟩
  exact ⟨(infinityFibreEquivPrimesOver (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)).symm P⟩
end QEC.Coding.AlgebraicGeometry.InverseAffinePlace
