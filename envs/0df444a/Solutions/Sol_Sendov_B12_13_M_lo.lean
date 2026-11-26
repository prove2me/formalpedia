-- Prove2me | solution 1 for Sendov.B12_13.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:22:07.954449+00:00
-- url     : https://prove2.me/submissions/afa44aee-e9ec-47f6-8958-a4d6d42fb897

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree12_13

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B12_13
namespace Sendov.B12_13
theorem _root_.solution : M 12 = 11 := by norm_num [M]
end Sendov.B12_13
