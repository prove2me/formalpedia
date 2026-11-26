-- Prove2me | solution 1 for TunnellMap.directSourceUnionEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:38:31.989793+00:00
-- url     : https://prove2.me/submissions/b7ff7e80-2cde-458b-90b7-00bb69e907c4

import Definitions.Def_TunnellMap_ResidualBalance
import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableDirect

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : Odd n) (d : DirectDomain n) :
    (directSourceUnionEquiv hn d).1 = directDomainRep d := by
  rcases d with d | d | d <;> rfl
end TunnellMap
