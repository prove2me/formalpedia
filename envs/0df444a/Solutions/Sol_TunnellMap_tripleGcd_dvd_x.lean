-- Prove2me | solution 1 for TunnellMap.tripleGcd_dvd_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:09.668309+00:00
-- url     : https://prove2.me/submissions/ffb63b72-7aac-42a1-9fd8-60228051c3d4

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution (v : Triple) : tripleGcd v ∣ v.x :=
  (gcd_dvd_left _ _).trans (gcd_dvd_left _ _)
end TunnellMap
