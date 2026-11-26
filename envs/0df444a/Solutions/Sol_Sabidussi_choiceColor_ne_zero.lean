-- Prove2me | solution 1 for Sabidussi.choiceColor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:36.363898+00:00
-- url     : https://prove2.me/submissions/9d07bc56-4745-41a9-b077-e9bd6b5a1415

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_LocalPattern
import Theorems.Thm_Sabidussi_tripleDifference_ne_zero


set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (c : Fin 3) : choiceColor c ≠ 0 := by
  apply tripleDifference_ne_zero
  norm_num [Prod.ext_iff]
end Sabidussi
