-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_19
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:10:12.221197+00:00
-- url     : https://prove2.me/submissions/8b3981bb-7d55-4a15-90dc-2ebcfa7436d4

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US015
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_19

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

lemma smallSupport13_19_oai : RowSquare [4,4,3,2] [6,3,3,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [4,3,3,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_19 smallT13_19 smallFlag13_19 smallChoices13_19
  change solveChoices smallChoices13_19 (.full [4,3,3,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,3,1,1,1] (Equiv.refl (Fin 13)) smallB13_19 smallT13_19) smallFlag13_19 ≠ 0
  rw [smallCert13_19]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_19_oai := @OAI.UniversalTensorSquare.smallSupport13_19_oai
