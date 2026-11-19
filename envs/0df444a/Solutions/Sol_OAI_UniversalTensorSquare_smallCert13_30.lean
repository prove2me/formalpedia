-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_30
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T05:09:32.561537+00:00
-- url     : https://prove2.me/submissions/eb3fc20a-a54c-4a0f-a920-87790ace381b

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US017

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

lemma smallCert13_30_oai : solveChoices smallChoices13_30 (.full [3,3,2,2,2,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,2,2,2,1] (Equiv.refl (Fin 13)) smallB13_30 smallT13_30) smallFlag13_30 = -20 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_30_oai := @OAI.UniversalTensorSquare.smallCert13_30_oai
