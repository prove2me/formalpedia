-- Prove2me | solution 1 for TunnellMap.primitiveDirectionExec_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:24.48408+00:00
-- url     : https://prove2.me/submissions/1ac5eeed-3eb8-4a2c-9d0d-6dc82411f77f

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
import Theorems.Thm_TunnellMap_primitivePartExec_eq

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirectionExec v = primitiveDirection v := by
  rw [primitiveDirectionExec, primitivePartExec_eq hv, primitiveDirection]
end TunnellMap
