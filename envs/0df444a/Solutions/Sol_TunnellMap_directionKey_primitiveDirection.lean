-- Prove2me | solution 1 for TunnellMap.directionKey_primitiveDirection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:48.141714+00:00
-- url     : https://prove2.me/submissions/7c5582f9-0918-4ce4-9221-c2236ec47f16

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
import Theorems.Thm_TunnellMap_directionKey_eq_iff
import Theorems.Thm_TunnellMap_primitiveDirection_idem
attribute [local simp] TunnellMap.primitiveDirection_idem



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {v : Triple}
    (hv : v ≠ ⟨0, 0, 0⟩) :
    directionKey (primitiveDirection v) = directionKey v := by
  rw [directionKey_eq_iff]
  exact primitiveDirection_idem hv
end TunnellMap
