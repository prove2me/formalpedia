-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_25
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:52:32.327432+00:00
-- url     : https://prove2.me/submissions/5cfed29a-9f45-40ce-b1dc-f37202564532

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US016

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_25_oai : solveChoices smallChoices13_25 (.full [4,2,2,2,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,2,2,2,1,1,1] (Equiv.refl (Fin 13)) smallB13_25 smallT13_25) smallFlag13_25 = -3 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_25_oai := @OAI.UniversalTensorSquare.smallCert13_25_oai
