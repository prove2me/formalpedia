-- Prove2me | solution 1 for TunnellMap.primitiveKey_eq_directionKey
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:42:39.643356+00:00
-- url     : https://prove2.me/submissions/44b2b329-d51a-4f93-94bc-d40939750caf

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
import Theorems.Thm_TunnellMap_tripleContent_eq_tripleGcd
import Theorems.Thm_TunnellMap_primitiveDirection_eq_self_of_content_one_of_oriented


set_option autoImplicit true
open TunnellMap
open Polynomial
namespace TunnellMap
theorem _root_.solution {v : Triple}
    (hcontent : tripleGcd v = 1) (horiented : FirstNonzeroPositive v) :
    primitiveKey v = directionKey v := by
  have hc : tripleContent v = 1 := by rw [tripleContent_eq_tripleGcd]; exact hcontent
  rw [directionKey, primitiveDirection_eq_self_of_content_one_of_oriented hc horiented,
    primitiveKey]
end TunnellMap
