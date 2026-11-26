-- Prove2me | solution 1 for TunnellMap.keyLtExec_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:26:30.563912+00:00
-- url     : https://prove2.me/submissions/6c31737d-eb14-4af2-9aad-219d5230b9e3

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
import Theorems.Thm_TunnellMap_DirectionKey_lt_iff_blt


set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution (k₁ k₂ : DirectionKey) :
    keyLtExec k₁ k₂ = true ↔ k₁ < k₂ :=
  (DirectionKey.lt_iff_blt k₁ k₂).symm
end TunnellMap
