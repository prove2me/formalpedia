-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_43
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:25:55.520487+00:00
-- url     : https://prove2.me/submissions/4cc98e8e-2b01-4502-af0a-1fab9a760976

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US018
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_43

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

lemma smallSupport13_43_oai : RowSquare [4,4,3,2] [4,4,4,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [4,3,3,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_43 smallT13_43 smallFlag13_43 smallChoices13_43
  change solveChoices smallChoices13_43 (.full [4,3,3,3]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,3,3] (Equiv.refl (Fin 13)) smallB13_43 smallT13_43) smallFlag13_43 ≠ 0
  rw [smallCert13_43]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_43_oai := @OAI.UniversalTensorSquare.smallSupport13_43_oai
