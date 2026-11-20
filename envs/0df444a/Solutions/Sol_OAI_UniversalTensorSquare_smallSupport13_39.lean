-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_39
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:25:26.80587+00:00
-- url     : https://prove2.me/submissions/50605e63-7834-494e-a198-2d5618e3610f

import Mathlib
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_39

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_39_oai : RowSquare [4,4,3,2] [11,1,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [3,1,1,1,1,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_39 smallT13_39 smallFlag13_39
  change solveCompact 13 (.full [3,1,1,1,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,1,1,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_39 smallT13_39) smallFlag13_39 ≠ 0
  rw [smallCert13_39]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_39_oai := @OAI.UniversalTensorSquare.smallSupport13_39_oai
