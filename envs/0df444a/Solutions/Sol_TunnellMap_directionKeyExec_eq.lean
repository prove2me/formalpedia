-- Prove2me | solution 1 for TunnellMap.directionKeyExec_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:18.141976+00:00
-- url     : https://prove2.me/submissions/47d00ec0-0851-4781-a13f-18a5f7a163c0

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
import Theorems.Thm_TunnellMap_primitiveDirectionExec_eq

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    directionKeyExec v = directionKey v := by
  rw [directionKeyExec, primitiveDirectionExec_eq hv, directionKey, primitiveKey]
end TunnellMap
