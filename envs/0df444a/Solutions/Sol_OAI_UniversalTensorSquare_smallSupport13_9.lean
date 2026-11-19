-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:28:42.735633+00:00
-- url     : https://prove2.me/submissions/53fbde6f-0af7-475a-a373-7f9dd0be2371

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US020
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_9

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_9_oai : RowSquare [4,4,3,2] [5,5,1,1,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [5,2,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_9 smallT13_9 smallFlag13_9 smallChoices13_9
  change solveChoices smallChoices13_9 (.full [5,2,2,2,2]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,2,2,2,2] (Equiv.refl (Fin 13)) smallB13_9 smallT13_9) smallFlag13_9 ≠ 0
  rw [smallCert13_9]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_9_oai := @OAI.UniversalTensorSquare.smallSupport13_9_oai
