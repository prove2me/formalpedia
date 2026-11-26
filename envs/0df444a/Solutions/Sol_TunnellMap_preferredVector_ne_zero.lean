-- Prove2me | solution 1 for TunnellMap.preferredVector_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:50.471345+00:00
-- url     : https://prove2.me/submissions/b1a00da8-74aa-4ecc-9d0a-612a62f71e4d

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
import Theorems.Thm_TunnellMap_plusVector_ne_zero
import Theorems.Thm_TunnellMap_minusVector_ne_zero
import Theorems.Thm_TunnellMap_preferredVector_eq_plus_or_minus

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (s : BResidual n) (t : AResidual n) :
    preferredVector s t ≠ ⟨0, 0, 0⟩ := by
  rcases preferredVector_eq_plus_or_minus s t with h | h
  · rw [h]
    exact plusVector_ne_zero s t
  · rw [h]
    exact minusVector_ne_zero s t
end TunnellMap
