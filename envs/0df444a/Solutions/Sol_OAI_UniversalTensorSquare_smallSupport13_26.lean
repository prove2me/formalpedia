-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_26
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:10:57.8412+00:00
-- url     : https://prove2.me/submissions/711517e5-1395-475e-81a7-1fc57fceb2d6

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US016
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_26 : solveChoices smallChoices13_26 (.full [4,2,2,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,2,2,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_26 smallT13_26) smallFlag13_26 = 4 := by
  decide +kernel

lemma smallSupport13_26_oai : RowSquare [4,4,3,2] [8,3,1,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [4,2,2,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_26 smallT13_26 smallFlag13_26 smallChoices13_26
  change solveChoices smallChoices13_26 (.full [4,2,2,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,2,2,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_26 smallT13_26) smallFlag13_26 ≠ 0
  rw [smallCert13_26]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_26_oai := @OAI.UniversalTensorSquare.smallSupport13_26_oai
