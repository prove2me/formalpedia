-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDifferential_eq_coordinate_smul_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:20:58.631199+00:00
-- url     : https://prove2.me/submissions/fadef0cc-ba43-407b-83a9-79310ac84c0b

import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SeparableDerivationExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution
    (omega : Differential k F) :
    omega = functionFieldDifferentialCoordinate (k := k) (F := F) omega •
      functionFieldDifferentialGenerator (k := k) (F := F) := by
  have h := congrArg (fun L : Differential k F →ₗ[F] Differential k F => L omega)
    (functionFieldDifferentialGeneratorMap_comp_coordinate (k := k) (F := F))
  simpa only [LinearMap.comp_apply, functionFieldDifferentialGeneratorMap,
    LinearMap.smulRight_apply, LinearMap.id_apply] using h.symm
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
