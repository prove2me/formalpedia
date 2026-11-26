-- Prove2me | solution 1 for TunnellMap.normalize_tripleGcd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:58.885913+00:00
-- url     : https://prove2.me/submissions/ade9ef11-bd90-4e36-91b7-6d5edbce5eb8

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection

set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution (v : Triple) : normalize (tripleGcd v) = tripleGcd v :=
  normalize_gcd _ _
end TunnellMap
