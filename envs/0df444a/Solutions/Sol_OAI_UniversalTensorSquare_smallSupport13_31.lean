-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_31
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:24:41.333963+00:00
-- url     : https://prove2.me/submissions/d87c132e-3535-4f87-9785-3c2cde5014d8

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US017
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_31

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

lemma smallSupport13_31_oai : RowSquare [4,4,3,2] [7,4,2] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [3,3,2,2,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_31 smallT13_31 smallFlag13_31 smallChoices13_31
  change solveChoices smallChoices13_31 (.full [3,3,2,2,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,2,2,1,1,1] (Equiv.refl (Fin 13)) smallB13_31 smallT13_31) smallFlag13_31 ≠ 0
  rw [smallCert13_31]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_31_oai := @OAI.UniversalTensorSquare.smallSupport13_31_oai
