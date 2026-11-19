-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_46
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:26:13.14379+00:00
-- url     : https://prove2.me/submissions/f9cb8250-f9d5-4f5f-87d8-c3a8afec576c

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US019
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_46

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_46_oai : RowSquare [4,4,3,2] [6,4,3] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [3,3,3,2,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_46 smallT13_46 smallFlag13_46 smallChoices13_46
  change solveChoices smallChoices13_46 (.full [3,3,3,2,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,3,2,1,1] (Equiv.refl (Fin 13)) smallB13_46 smallT13_46) smallFlag13_46 ≠ 0
  rw [smallCert13_46]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_46_oai := @OAI.UniversalTensorSquare.smallSupport13_46_oai
