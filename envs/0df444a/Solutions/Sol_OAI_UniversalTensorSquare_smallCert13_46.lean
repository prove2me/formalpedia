-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_46
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:56:17.890501+00:00
-- url     : https://prove2.me/submissions/67b54f4c-b961-47bc-9949-78a7f61e29f7

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US019

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_46_oai : solveChoices smallChoices13_46 (.full [3,3,3,2,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,3,2,1,1] (Equiv.refl (Fin 13)) smallB13_46 smallT13_46) smallFlag13_46 = -8 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_46_oai := @OAI.UniversalTensorSquare.smallCert13_46_oai
