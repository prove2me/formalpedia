-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:25:03.860584+00:00
-- url     : https://prove2.me/submissions/8408ea7e-d262-4785-bc1f-2f7998e0aeca

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US018
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_35

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_35_oai : RowSquare [4,4,3,2] [7,5,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [3,2,2,2,2,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_35 smallT13_35 smallFlag13_35 smallChoices13_35
  change solveChoices smallChoices13_35 (.full [3,2,2,2,2,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,2,2,2,2,1,1] (Equiv.refl (Fin 13)) smallB13_35 smallT13_35) smallFlag13_35 ≠ 0
  rw [smallCert13_35]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_35_oai := @OAI.UniversalTensorSquare.smallSupport13_35_oai
