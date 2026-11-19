-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_47
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:26:19.029873+00:00
-- url     : https://prove2.me/submissions/0d3ccabf-232e-4b75-9329-34f4781c6de7

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US019
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_47

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

lemma smallSupport13_47_oai : RowSquare [4,4,3,2] [7,6] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [2,2,2,2,2,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_47 smallT13_47 smallFlag13_47 smallChoices13_47
  change solveChoices smallChoices13_47 (.full [2,2,2,2,2,2,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [2,2,2,2,2,2,1] (Equiv.refl (Fin 13)) smallB13_47 smallT13_47) smallFlag13_47 ≠ 0
  rw [smallCert13_47]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_47_oai := @OAI.UniversalTensorSquare.smallSupport13_47_oai
