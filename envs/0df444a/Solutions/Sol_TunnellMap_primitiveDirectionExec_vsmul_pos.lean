-- Prove2me | solution 1 for TunnellMap.primitiveDirectionExec_vsmul_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:47.355748+00:00
-- url     : https://prove2.me/submissions/2491e462-e576-4af2-a27c-68c7d9c827ed

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
import Theorems.Thm_TunnellMap_primitivePartExec_vsmul_pos

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution {c : ℤ} (hc : 0 < c) (v : Triple) :
    primitiveDirectionExec (vsmul c v) = primitiveDirectionExec v := by
  unfold primitiveDirectionExec
  rw [primitivePartExec_vsmul_pos hc]
end TunnellMap
