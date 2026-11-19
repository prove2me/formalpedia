-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_33
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:52:54.818428+00:00
-- url     : https://prove2.me/submissions/4815fee3-5060-4938-a0d6-e89e1ecb4800

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US017

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_33_oai : solveChoices smallChoices13_33 (.full [3,3,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_33 smallT13_33) smallFlag13_33 = -24 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_33_oai := @OAI.UniversalTensorSquare.smallCert13_33_oai
