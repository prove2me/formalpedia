-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_15
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:09:48.985428+00:00
-- url     : https://prove2.me/submissions/2334a7f6-4b48-4963-a0e1-78417ffb5da1

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US014
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_15

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_15_oai : RowSquare [4,4,3,2] [5,4,2,2] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [4,4,2,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_15 smallT13_15 smallFlag13_15 smallChoices13_15
  change solveChoices smallChoices13_15 (.full [4,4,2,2,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,4,2,2,1] (Equiv.refl (Fin 13)) smallB13_15 smallT13_15) smallFlag13_15 ≠ 0
  rw [smallCert13_15]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_15_oai := @OAI.UniversalTensorSquare.smallSupport13_15_oai
