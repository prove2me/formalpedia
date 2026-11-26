-- Prove2me | solution 1 for TunnellMap.etaPoint_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:08:47.900617+00:00
-- url     : https://prove2.me/submissions/7f51faa5-8965-4e39-8e92-e78fdc86374c

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution {n : ℤ} (s : BResidual n) (t : AResidual n) :
    etaPoint s t = 1 ∨ etaPoint s t = -1 := by
  unfold etaPoint; split
  · exact Or.inl rfl
  · exact Or.inr rfl
end TunnellMap
