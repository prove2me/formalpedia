-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_28
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:24:18.485083+00:00
-- url     : https://prove2.me/submissions/b3dc2e22-2abb-4eb7-b8f4-8120b4f6e21b

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US016
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_28 : solveChoices smallChoices13_28 (.full [4,1,1,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,1,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_28 smallT13_28) smallFlag13_28 = -4 := by
  decide +kernel

lemma smallSupport13_28_oai : RowSquare [4,4,3,2] [10,1,1,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [4,1,1,1,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_28 smallT13_28 smallFlag13_28 smallChoices13_28
  change solveChoices smallChoices13_28 (.full [4,1,1,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,1,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_28 smallT13_28) smallFlag13_28 ≠ 0
  rw [smallCert13_28]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_28_oai := @OAI.UniversalTensorSquare.smallSupport13_28_oai
