-- Prove2me | solution 2 for QEC.Semantics.QuantumChannel.mapDensity_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:43:06.33956+00:00
-- url     : https://prove2.me/submissions/b357d9df-0985-4a42-9ac9-d903ce302e3a

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
    LinearMap.IsPositive (Φ.mapDensity rho).toOperator :=
  (Φ.mapDensity rho).positive
end QEC.Semantics.QuantumChannel
