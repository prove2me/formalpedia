-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:26:42.894023+00:00
-- url     : https://prove2.me/submissions/5eb77934-0df2-41f2-8dc1-b4dda8a3f566

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US020
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_50

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_50_oai : RowSquare [4,4,3,2] [11,2] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [2,2,1,1,1,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_50 smallT13_50 smallFlag13_50 smallChoices13_50
  change solveChoices smallChoices13_50 (.full [2,2,1,1,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [2,2,1,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_50 smallT13_50) smallFlag13_50 ≠ 0
  rw [smallCert13_50]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_50_oai := @OAI.UniversalTensorSquare.smallSupport13_50_oai
