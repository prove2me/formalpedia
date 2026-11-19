-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_37
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:25:15.286441+00:00
-- url     : https://prove2.me/submissions/71965a52-68e5-4fc5-b9bc-c8d45363152b

import Mathlib
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_37

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

lemma smallSupport13_37_oai : RowSquare [4,4,3,2] [9,3,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [3,2,2,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_37 smallT13_37 smallFlag13_37
  change solveCompact 13 (.full [3,2,2,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,2,2,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_37 smallT13_37) smallFlag13_37 ≠ 0
  rw [smallCert13_37]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_37_oai := @OAI.UniversalTensorSquare.smallSupport13_37_oai
