-- Prove2me | solution 1 for QEC.Semantics.UnitaryTransport.conjDensity_positive
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:52:44.787872+00:00
-- url     : https://prove2.me/submissions/7d8c635f-bec3-4f69-a797-208fafeee266

-- ID: 20a690cf-42c3-473b-8f61-a7e697a87c97 | NAME: QEC.Semantics.UnitaryTransport.conjDensity_positive | 未本地编译验证
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
    LinearMap.IsPositive (U.conjDensity rho).toOperator := by
  exact (U.conjDensity rho).positive
