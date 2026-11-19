-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:06:38.741685+00:00
-- url     : https://prove2.me/submissions/f51f67ad-0743-46b9-a791-ee93fb10c66b

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US014
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_10

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_10_oai : RowSquare [4,4,3,2] [6,4,1,1,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [5,2,2,2,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_10 smallT13_10 smallFlag13_10 smallChoices13_10
  change solveChoices smallChoices13_10 (.full [5,2,2,2,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,2,2,2,1,1] (Equiv.refl (Fin 13)) smallB13_10 smallT13_10) smallFlag13_10 ≠ 0
  rw [smallCert13_10]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_10_oai := @OAI.UniversalTensorSquare.smallSupport13_10_oai
