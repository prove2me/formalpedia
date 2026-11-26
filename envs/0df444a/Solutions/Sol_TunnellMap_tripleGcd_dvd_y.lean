-- Prove2me | solution 1 for TunnellMap.tripleGcd_dvd_y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:38.019555+00:00
-- url     : https://prove2.me/submissions/b60aec7a-9ce1-43f5-bb54-49615eaaf6ef

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution (v : Triple) : tripleGcd v ∣ v.y :=
  (gcd_dvd_left _ _).trans (gcd_dvd_right _ _)
end TunnellMap
