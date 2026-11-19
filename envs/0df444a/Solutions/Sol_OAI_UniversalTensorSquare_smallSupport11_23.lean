-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_23
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:02:45.889402+00:00
-- url     : https://prove2.me/submissions/9b67b4dc-b028-4242-a127-959824c81a43

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US013
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert11_23

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport11_23_oai : RowSquare [4,3,3,1] [6,5] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [2,2,2,2,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_23 smallT11_23 smallFlag11_23 smallChoices11_23
  change solveChoices smallChoices11_23 (.full [2,2,2,2,2,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [2,2,2,2,2,1] (Equiv.refl (Fin 11)) smallB11_23 smallT11_23) smallFlag11_23 ≠ 0
  rw [smallCert11_23]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_23_oai := @OAI.UniversalTensorSquare.smallSupport11_23_oai
