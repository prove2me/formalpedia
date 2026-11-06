-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.mapDensity_trace
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:48:25.013469+00:00
-- url     : https://prove2.me/submissions/cb228c48-c2a7-43de-a4f4-3ff662bfe2e7

-- ID: 2b7842ca-47cd-4f98-bcca-acf07d40febe | NAME: QEC.Semantics.QuantumChannel.mapDensity_trace | 未本地编译验证
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
    LinearMap.trace Complex K (Φ.mapDensity rho).toOperator = 1 := by
  exact (Φ.mapDensity rho).trace_one
