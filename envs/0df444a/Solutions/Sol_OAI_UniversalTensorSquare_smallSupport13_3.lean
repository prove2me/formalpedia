-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:24:29.949653+00:00
-- url     : https://prove2.me/submissions/1bc27b55-9f95-4fbe-8ba7-e2e104d2ac41

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US015
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_3

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_ChoiceCertificates13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choice certificates in degree thirteen. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_3_oai : RowSquare [4,4,3,2] [8,1,1,1,1,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [6,1,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_3 smallT13_3 smallFlag13_3 smallChoices13_3
  change solveChoices smallChoices13_3 (.full [6,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [6,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_3 smallT13_3) smallFlag13_3 ≠ 0
  rw [smallCert13_3]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_3_oai := @OAI.UniversalTensorSquare.smallSupport13_3_oai
