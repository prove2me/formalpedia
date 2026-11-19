-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_30
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:24:35.691959+00:00
-- url     : https://prove2.me/submissions/0b20bf73-c3f3-4598-b960-5e0c9843a1a2

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US017
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_30

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_30_oai : RowSquare [4,4,3,2] [6,5,2] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [3,3,2,2,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_30 smallT13_30 smallFlag13_30 smallChoices13_30
  change solveChoices smallChoices13_30 (.full [3,3,2,2,2,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,2,2,2,1] (Equiv.refl (Fin 13)) smallB13_30 smallT13_30) smallFlag13_30 ≠ 0
  rw [smallCert13_30]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_30_oai := @OAI.UniversalTensorSquare.smallSupport13_30_oai
