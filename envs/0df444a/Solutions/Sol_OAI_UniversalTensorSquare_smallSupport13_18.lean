-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_18
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:10:06.639219+00:00
-- url     : https://prove2.me/submissions/44806228-ed37-4cb9-bdc3-8acbdceb534b

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US015
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_18 : solveChoices smallChoices13_18 (.full [4,3,3,2,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,3,2,1] (Equiv.refl (Fin 13)) smallB13_18 smallT13_18) smallFlag13_18 = -19 := by
  decide +kernel

lemma smallSupport13_18_oai : RowSquare [4,4,3,2] [5,4,3,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [4,3,3,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_18 smallT13_18 smallFlag13_18 smallChoices13_18
  change solveChoices smallChoices13_18 (.full [4,3,3,2,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,3,2,1] (Equiv.refl (Fin 13)) smallB13_18 smallT13_18) smallFlag13_18 ≠ 0
  rw [smallCert13_18]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_18_oai := @OAI.UniversalTensorSquare.smallSupport13_18_oai
