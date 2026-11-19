-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:28:36.816186+00:00
-- url     : https://prove2.me/submissions/fee8d968-5c67-4e88-8eec-62680c6e825f

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US020
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_8

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

lemma smallSupport13_8_oai : RowSquare [4,4,3,2] [7,2,2,1,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [5,3,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_8 smallT13_8 smallFlag13_8 smallChoices13_8
  change solveChoices smallChoices13_8 (.full [5,3,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,3,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_8 smallT13_8) smallFlag13_8 ≠ 0
  rw [smallCert13_8]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_8_oai := @OAI.UniversalTensorSquare.smallSupport13_8_oai
