-- Prove2me | solution 1 for TunnellMap.tripleGcd_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:42:38.880316+00:00
-- url     : https://prove2.me/submissions/c2fa45fb-403a-4063-b77c-2b8009b43ca1

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
import Theorems.Thm_TunnellMap_tripleContent_eq_tripleGcd
import Theorems.Thm_TunnellMap_tripleContent_ne_zero


set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) : tripleGcd v ≠ 0 := by
  rw [← tripleContent_eq_tripleGcd]
  exact tripleContent_ne_zero hv
end TunnellMap
