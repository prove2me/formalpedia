-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_33
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:24:52.675928+00:00
-- url     : https://prove2.me/submissions/2d230890-e388-4f32-9504-039340d1508a

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US017
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_33

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

lemma smallSupport13_33_oai : RowSquare [4,4,3,2] [9,2,2] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [3,3,1,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_33 smallT13_33 smallFlag13_33 smallChoices13_33
  change solveChoices smallChoices13_33 (.full [3,3,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_33 smallT13_33) smallFlag13_33 ≠ 0
  rw [smallCert13_33]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_33_oai := @OAI.UniversalTensorSquare.smallSupport13_33_oai
