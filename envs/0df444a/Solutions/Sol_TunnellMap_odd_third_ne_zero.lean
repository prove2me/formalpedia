-- Prove2me | solution 1 for TunnellMap.odd_third_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:53:59.404775+00:00
-- url     : https://prove2.me/submissions/00ce0bda-97f0-40cc-8f7b-7aa88a488e07

import Definitions.Def_TunnellMap_QuarterTurns
import Definitions.Def_TunnellMap_Midpoint

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {p : Triple} (hp : Odd p.z) : p ≠ ⟨0, 0, 0⟩ := by
  intro h
  have hz : p.z = 0 := congrArg Triple.z h
  rw [hz] at hp
  exact Int.not_odd_zero hp
end TunnellMap
