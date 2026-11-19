-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_41
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:25:43.80269+00:00
-- url     : https://prove2.me/submissions/db6554bc-76ab-4d16-b722-87005f183b2f

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US014
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_41

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

lemma smallSupport13_41_oai : RowSquare [4,4,3,2] [12,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [2,1,1,1,1,1,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_41 smallT13_41 smallFlag13_41 smallChoices13_41
  change solveChoices smallChoices13_41 (.full [2,1,1,1,1,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [2,1,1,1,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_41 smallT13_41) smallFlag13_41 ≠ 0
  rw [smallCert13_41]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_41_oai := @OAI.UniversalTensorSquare.smallSupport13_41_oai
