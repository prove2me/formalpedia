-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_42
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:25:49.799917+00:00
-- url     : https://prove2.me/submissions/0f01d526-b4ce-479a-8ebf-30b74607f60a

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US017
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_42

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 10. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_42_oai : RowSquare [4,4,3,2] [4,4,3,2] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [4,4,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_42 smallT13_42 smallFlag13_42 smallChoices13_42
  change solveChoices smallChoices13_42 (.full [4,4,3,2]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,4,3,2] (Equiv.refl (Fin 13)) smallB13_42 smallT13_42) smallFlag13_42 ≠ 0
  rw [smallCert13_42]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_42_oai := @OAI.UniversalTensorSquare.smallSupport13_42_oai
