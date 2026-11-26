-- Prove2me | solution 1 for TunnellMap.DirectionKey.lt_iff_blt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:24:02.449144+00:00
-- url     : https://prove2.me/submissions/44b3bbcb-f1e2-4f61-a765-0d1a231c6f39

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey

set_option autoImplicit true
open TunnellMap
open TunnellMap.DirectionKey
namespace TunnellMap.DirectionKey
theorem _root_.solution (a b : DirectionKey) : a < b ↔ blt a b = true :=
  (blt_iff_lex a b).symm
end TunnellMap.DirectionKey
