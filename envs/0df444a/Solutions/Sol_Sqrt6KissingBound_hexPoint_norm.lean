-- Prove2me | solution 1 for Sqrt6KissingBound.hexPoint_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:27:30.508267+00:00
-- url     : https://prove2.me/submissions/090e9658-f96a-41be-8834-037d533d904a

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
import Theorems.Thm_Sqrt6KissingBound_planePoint_norm_eq_one
section
namespace Sqrt6KissingBound
noncomputable section
private lemma s3_sq_opt : s3_opt ^ 2 = 3 := by norm_num [s3_opt]
end
end Sqrt6KissingBound
end

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution (i : Fin 6) : ‖hexPoint i‖ = 1 := by
  fin_cases i <;> apply planePoint_norm_eq_one <;> nlinarith [s3_sq_opt]
end Sqrt6KissingBound
