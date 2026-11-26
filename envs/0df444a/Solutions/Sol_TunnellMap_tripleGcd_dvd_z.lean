-- Prove2me | solution 1 for TunnellMap.tripleGcd_dvd_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:48.093575+00:00
-- url     : https://prove2.me/submissions/8d4085a2-4aee-41f0-9422-58a1de3fed57

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution (v : Triple) : tripleGcd v ∣ v.z := gcd_dvd_right _ _
end TunnellMap
