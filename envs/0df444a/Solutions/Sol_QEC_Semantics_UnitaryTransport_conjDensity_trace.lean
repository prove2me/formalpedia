-- Prove2me | solution 1 for QEC.Semantics.UnitaryTransport.conjDensity_trace
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:55:43.708209+00:00
-- url     : https://prove2.me/submissions/d43f047c-f9c7-406d-bb07-ac9227db7c9b

-- ID: 0a3d43d2-65dc-451a-b13c-9aa5d73c9ae3 | NAME: QEC.Semantics.UnitaryTransport.conjDensity_trace | 未本地编译验证
import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.UnitaryTransport
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]

theorem solution (U : UnitaryTransport H K)
    (rho : DensityOperator H) :
    LinearMap.trace Complex K (U.conjDensity rho).toOperator = 1 := by
  exact (U.conjDensity rho).trace_one
