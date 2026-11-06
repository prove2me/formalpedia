-- Prove2me | solution 1 for QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:47:38.590837+00:00
-- url     : https://prove2.me/submissions/3bd7a7ce-49cc-437b-b114-41c408da714c

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Channels_Core

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
namespace QEC.Semantics
theorem _root_.solution (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator (CompositeSystem H K)) :
    (partialTraceRightRaw_mapDensity H K rho).toOperator =
      (partialTraceRightRaw H K) rho.toOperator :=
  rfl
end QEC.Semantics
