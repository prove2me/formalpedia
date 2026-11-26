-- Prove2me | solution 1 for TunnellMap.FreeInvolution.card_eq_twice_orbit_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:59.007381+00:00
-- url     : https://prove2.me/submissions/4b4dd400-9b5c-4e62-83a5-96b5eba83653

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_Antipodal

set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
variable [Fintype X] [DecidableEq X]
namespace TunnellMap.FreeInvolution
theorem _root_.solution :
    Fintype.card X = 2 * Fintype.card I.Orbit := by
  rw [Fintype.card_congr I.orbitBoolEquiv, Fintype.card_prod, Fintype.card_bool]
  omega
end TunnellMap.FreeInvolution
