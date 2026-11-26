-- Prove2me | solution 1 for Sendov.B30_31.M_lo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:30:29.784101+00:00
-- url     : https://prove2.me/submissions/0720ac41-3b93-4dd4-9204-334e242d5198

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree30_31

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B30_31
namespace Sendov.B30_31
theorem _root_.solution : M 30 = 29 := by norm_num [M]
end Sendov.B30_31
