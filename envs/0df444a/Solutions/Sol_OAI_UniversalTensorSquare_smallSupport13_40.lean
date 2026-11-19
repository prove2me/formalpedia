-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_40
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:25:38.091147+00:00
-- url     : https://prove2.me/submissions/b8cf983a-ee3d-4d20-928c-819d6223b211

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US018
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_40

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 10. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_40_oai : RowSquare [4,4,3,2] [10,3] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [2,2,2,1,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_40 smallT13_40 smallFlag13_40 smallChoices13_40
  change solveChoices smallChoices13_40 (.full [2,2,2,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [2,2,2,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_40 smallT13_40) smallFlag13_40 ≠ 0
  rw [smallCert13_40]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_40_oai := @OAI.UniversalTensorSquare.smallSupport13_40_oai
