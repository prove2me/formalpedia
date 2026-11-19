-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:06:56.254505+00:00
-- url     : https://prove2.me/submissions/12dd8cab-328a-465d-b2b6-a7df4b5ee0cf

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US014
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_13

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

lemma smallSupport13_13_oai : RowSquare [4,4,3,2] [9,1,1,1,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [5,1,1,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_13 smallT13_13 smallFlag13_13 smallChoices13_13
  change solveChoices smallChoices13_13 (.full [5,1,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_13 smallT13_13) smallFlag13_13 ≠ 0
  rw [smallCert13_13]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_13_oai := @OAI.UniversalTensorSquare.smallSupport13_13_oai
