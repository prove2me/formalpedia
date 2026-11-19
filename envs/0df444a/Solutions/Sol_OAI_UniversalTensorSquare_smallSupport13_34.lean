-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_34
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:24:58.273422+00:00
-- url     : https://prove2.me/submissions/4454e25e-28e3-4201-a052-9f59b6af27e9

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US018
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_34

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

lemma smallSupport13_34_oai : RowSquare [4,4,3,2] [6,6,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [3,2,2,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_34 smallT13_34 smallFlag13_34 smallChoices13_34
  change solveChoices smallChoices13_34 (.full [3,2,2,2,2,2]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,2,2,2,2,2] (Equiv.refl (Fin 13)) smallB13_34 smallT13_34) smallFlag13_34 ≠ 0
  rw [smallCert13_34]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_34_oai := @OAI.UniversalTensorSquare.smallSupport13_34_oai
