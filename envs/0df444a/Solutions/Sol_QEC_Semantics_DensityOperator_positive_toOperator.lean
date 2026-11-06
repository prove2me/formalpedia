-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.positive_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:58:14.427116+00:00
-- url     : https://prove2.me/submissions/cff45dae-14ed-4d6c-b648-48273be718d6

-- ID: c1db8317-4d51-4881-be05-83614e424fd4 | NAME: QEC.Semantics.DensityOperator.positive_toOperator | 未本地编译验证
import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem solution (rho : DensityOperator H) :
    LinearMap.IsPositive rho.toOperator := by
  exact rho.positive
