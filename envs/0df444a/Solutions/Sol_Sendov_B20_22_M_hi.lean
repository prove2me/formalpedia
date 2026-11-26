-- Prove2me | solution 1 for Sendov.B20_22.M_hi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:26:07.422799+00:00
-- url     : https://prove2.me/submissions/2f63d63c-53ee-46d7-b197-9b07d088663b

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree20_22

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B20_22
namespace Sendov.B20_22
theorem _root_.solution : M 22 = 21 := by norm_num [M]
end Sendov.B20_22
