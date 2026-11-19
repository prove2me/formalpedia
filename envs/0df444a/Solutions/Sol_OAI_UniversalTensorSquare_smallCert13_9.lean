-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:59:12.27059+00:00
-- url     : https://prove2.me/submissions/92197657-09ce-4e87-9fe6-9308ce3b9848

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US020

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

lemma smallCert13_9_oai : solveChoices smallChoices13_9 (.full [5,2,2,2,2]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,2,2,2,2] (Equiv.refl (Fin 13)) smallB13_9 smallT13_9) smallFlag13_9 = 28 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_9_oai := @OAI.UniversalTensorSquare.smallCert13_9_oai
