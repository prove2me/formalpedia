-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.mapDensity_positive
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:50:53.829367+00:00
-- url     : https://prove2.me/submissions/d15acb9a-3810-434c-bdb1-314a0901619a

-- ID: c6b64e78-42b8-4bb3-b87e-3b4f1caafd9f | NAME: QEC.Semantics.QuantumChannel.mapDensity_positive | 未本地编译验证
import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Channels_Core
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
open QEC.Semantics.QuantumChannel
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem solution (Φ : QuantumChannel H K)
    (rho : DensityOperator H) :
    LinearMap.IsPositive (Φ.mapDensity rho).toOperator := by
  exact (Φ.mapDensity rho).positive
