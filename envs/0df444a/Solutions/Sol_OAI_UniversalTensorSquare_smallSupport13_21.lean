-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_21
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:10:29.521184+00:00
-- url     : https://prove2.me/submissions/8026af2b-4670-4ccb-bdc0-bda130c1beda

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_21

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_21_oai : RowSquare [4,4,3,2] [6,4,2,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [4,3,2,2,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_21 smallT13_21 smallFlag13_21
  change solveCompact 13 (.full [4,3,2,2,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,2,2,1,1] (Equiv.refl (Fin 13)) smallB13_21 smallT13_21) smallFlag13_21 ≠ 0
  rw [smallCert13_21]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_21_oai := @OAI.UniversalTensorSquare.smallSupport13_21_oai
