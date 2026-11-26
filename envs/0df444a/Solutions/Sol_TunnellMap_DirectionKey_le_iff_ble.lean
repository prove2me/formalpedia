-- Prove2me | solution 1 for TunnellMap.DirectionKey.le_iff_ble
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:49.849921+00:00
-- url     : https://prove2.me/submissions/47106f97-614a-4752-9f4c-e175ad75e546

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey

set_option autoImplicit true
open TunnellMap
open TunnellMap.DirectionKey
namespace TunnellMap.DirectionKey
theorem _root_.solution (a b : DirectionKey) : a ≤ b ↔ ble a b = true :=
  (ble_iff_lex a b).symm
end TunnellMap.DirectionKey
