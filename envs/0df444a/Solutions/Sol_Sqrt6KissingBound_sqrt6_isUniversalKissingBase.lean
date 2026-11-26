-- Prove2me | solution 1 for Sqrt6KissingBound.sqrt6_isUniversalKissingBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:35:46.664113+00:00
-- url     : https://prove2.me/submissions/66b90a14-33c1-4947-90c2-b7ce1097e8e8

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
import Theorems.Thm_Sqrt6KissingBound_kissingConfiguration_card_le_sqrt6_pow


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution :
    IsUniversalKissingBase (Real.sqrt 6) := by
  constructor
  · exact Real.sqrt_nonneg 6
  · intro n hn X hX
    exact kissingConfiguration_card_le_sqrt6_pow hn X hX
end Sqrt6KissingBound
