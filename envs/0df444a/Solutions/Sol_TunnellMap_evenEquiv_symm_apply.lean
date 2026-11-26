-- Prove2me | solution 1 for TunnellMap.evenEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:10.569856+00:00
-- url     : https://prove2.me/submissions/ecbee9c6-309f-4efb-b7e6-414ff767c225

import Mathlib
import Definitions.Def_TunnellMap_Basic

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (n : ℤ) (p : ARep n) :
    (evenEquiv n).symm p = aToEven p :=
  rfl
end TunnellMap
