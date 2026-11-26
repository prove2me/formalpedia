-- Prove2me | solution 1 for TunnellMap.plus_minus_keys_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:31:28.38664+00:00
-- url     : https://prove2.me/submissions/9598e9af-1556-4058-a2e2-8200373c1c01

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
import Theorems.Thm_TunnellMap_directionKey_eq_iff
import Theorems.Thm_TunnellMap_plus_minus_directions_ne

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (s : BResidual n) (t : AResidual n) :
    directionKey (plusVector s t) ≠ directionKey (minusVector s t) := by
  intro h
  exact plus_minus_directions_ne s t (directionKey_eq_iff.mp h)
end TunnellMap
