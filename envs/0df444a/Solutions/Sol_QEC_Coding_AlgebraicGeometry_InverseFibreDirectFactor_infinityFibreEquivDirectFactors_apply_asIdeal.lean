-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:37:57.189854+00:00
-- url     : https://prove2.me/submissions/6308728f-f2d7-4bca-b2e7-436e6018d607

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_FibreDirectFactor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor
open scoped Polynomial RatFunc
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
local notation3 "inverseRationalAlgebra" =>
  InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inversePolynomialAlgebra" =>
  InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseScalarTower" =>
  InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseFunctionField" =>
  InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldFunctionField := oldFunctionField) k F
local notation3 "inverseIsSeparable" =>
  InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldSeparable := oldSeparable) k F
omit oldPolynomialAlgebra oldScalarTower
namespace QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor
theorem _root_.solution
    (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    ((infinityFibreEquivDirectFactors
      (oldRationalAlgebra := oldRationalAlgebra) k F D :
        (factors (Ideal.map
          (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))
          (Polynomial.idealX k).asIdeal)).toFinset) :
      Ideal (_root_.FunctionField.ringOfIntegers k F)) = D.1.asIdeal := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  let B : Type _ := _root_.FunctionField.ringOfIntegers k F
  letI : Module.IsTorsionFree k[X] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
  change
    ((InverseAffinePlace.infinityFibreEquivPrimesOver
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) k F D :
        (InverseAffinePlace.infinityBasePrime k).primesOver B) : Ideal B) =
      D.1.asIdeal
  rfl
end QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor
