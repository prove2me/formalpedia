-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDerivation_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:42:06.733861+00:00
-- url     : https://prove2.me/submissions/b26dfe3c-b593-4eaf-9e3f-46d13abb2e7e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
noncomputable section
variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]
variable {L : Type*} [Field L] [Algebra k L] [Algebra (RatFunc k) L]
    [IsScalarTower k (RatFunc k) L]
    [Algebra.IsSeparable (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    [Algebra K L] [IsScalarTower k K L] [IsScalarTower (RatFunc k) K L]
omit [Finite k]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution (x : K) :
    functionFieldDerivation (k := k) (F := L) (algebraMap K L x) =
      algebraMap K L (functionFieldDerivation (k := k) (F := K) x) := by
  let Du := functionFieldDerivation (k := k) (F := L)
  let Dl := functionFieldDerivation (k := k) (F := K)
  let Dr : Derivation k K L := Du.compAlgebraMap K
  let Dt : Derivation k K L := (Algebra.ofId K L).toLinearMap.compDer Dl
  have h : Dr = Dt := by
    apply SeparableDerivationExtension.extension_unique
    apply (RatFuncDerivation.rationalDerivationEquiv (k := k) (M := L)).injective
    change Du (algebraMap K L (algebraMap (RatFunc k) K RatFunc.X)) =
      algebraMap K L (Dl (algebraMap (RatFunc k) K RatFunc.X))
    rw [← IsScalarTower.algebraMap_apply (RatFunc k) K L]
    rw [functionFieldDerivation_apply_X, functionFieldDerivation_apply_X, map_one]
  exact Derivation.congr_fun h x
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
