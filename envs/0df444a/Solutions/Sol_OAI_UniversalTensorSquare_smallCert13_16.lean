-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_16
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:51:46.598374+00:00
-- url     : https://prove2.me/submissions/6e050e3c-3b5c-46ce-98ca-d595fc6d1576

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US014

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

lemma smallCert13_16_oai : solveChoices smallChoices13_16 (.full [4,4,2,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,4,2,1,1,1] (Equiv.refl (Fin 13)) smallB13_16 smallT13_16) smallFlag13_16 = 1 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_16_oai := @OAI.UniversalTensorSquare.smallCert13_16_oai
