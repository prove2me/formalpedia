-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_25
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:10:52.011972+00:00
-- url     : https://prove2.me/submissions/5948688f-c826-494c-83be-ca6dcbfc9baf

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US016
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_25

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

lemma smallSupport13_25_oai : RowSquare [4,4,3,2] [7,4,1,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [4,2,2,2,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_25 smallT13_25 smallFlag13_25 smallChoices13_25
  change solveChoices smallChoices13_25 (.full [4,2,2,2,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,2,2,2,1,1,1] (Equiv.refl (Fin 13)) smallB13_25 smallT13_25) smallFlag13_25 ≠ 0
  rw [smallCert13_25]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_25_oai := @OAI.UniversalTensorSquare.smallSupport13_25_oai
