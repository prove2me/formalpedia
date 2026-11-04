-- Prove2me | solution 1 for ThreeSumApsp.strassen_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:04:51.577553+00:00
-- url     : https://prove2.me/submissions/fc47d444-4175-44ee-92f8-a4c31d90d868

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Submission_ThreeSumApsp_Sec3_Parameters

set_option autoImplicit false
section
open ThreeSumApsp
namespace ThreeSumApsp
theorem _root_.solution (n : ℕ) : 0 ≤ strassen n := Real.rpow_nonneg n.cast_nonneg _
end ThreeSumApsp
