-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_49
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:26:31.225324+00:00
-- url     : https://prove2.me/submissions/cce159ab-baf0-4b33-9fd1-9efa95baa1c4

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US019
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_49

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

lemma smallSupport13_49_oai : RowSquare [4,4,3,2] [9,4] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [2,2,2,2,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_49 smallT13_49 smallFlag13_49 smallChoices13_49
  change solveChoices smallChoices13_49 (.full [2,2,2,2,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [2,2,2,2,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_49 smallT13_49) smallFlag13_49 ≠ 0
  rw [smallCert13_49]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_49_oai := @OAI.UniversalTensorSquare.smallSupport13_49_oai
