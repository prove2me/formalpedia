-- Prove2me | solution 1 for Sabidussi.sum_choiceColor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:43.19842+00:00
-- url     : https://prove2.me/submissions/e79a295d-89ff-4bec-a876-adcb966264b9

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_LocalPattern
import Theorems.Thm_Sabidussi_sum_tripleDifference


set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution : ∑ c, choiceColor c = 0 := by
  exact sum_tripleDifference (1, 0)
end Sabidussi
