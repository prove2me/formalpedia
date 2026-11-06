-- Prove2me | solution 2 for QEC.Semantics.QuantumChannel.mapDensity_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:43:07.178315+00:00
-- url     : https://prove2.me/submissions/6a0a0661-e65e-4157-99af-80a7f8654178

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
namespace QEC.Semantics.QuantumChannel
theorem _root_.solution (Φ : QuantumChannel H K)
    (rho : DensityOperator H) :
    LinearMap.trace Complex K (Φ.mapDensity rho).toOperator = 1 :=
  (Φ.mapDensity rho).trace_one
end QEC.Semantics.QuantumChannel
