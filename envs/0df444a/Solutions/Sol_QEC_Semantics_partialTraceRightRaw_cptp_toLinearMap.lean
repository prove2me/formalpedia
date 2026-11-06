-- Prove2me | solution 1 for QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:47:21.007186+00:00
-- url     : https://prove2.me/submissions/bc14ad0f-100b-4f5b-9126-810af9117d16

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
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    (partialTraceRightRaw_cptp H K).toLinearMap = partialTraceRightRaw H K :=
  rfl
end QEC.Semantics
