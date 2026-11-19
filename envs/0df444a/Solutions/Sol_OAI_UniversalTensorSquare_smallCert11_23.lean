-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert11_23
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:48:27.695141+00:00
-- url     : https://prove2.me/submissions/265a9cad-ebb3-44d5-83a6-c024a6c651ce

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US013

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert11_23_oai : solveChoices smallChoices11_23 (.full [2,2,2,2,2,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [2,2,2,2,2,1] (Equiv.refl (Fin 11)) smallB11_23 smallT11_23) smallFlag11_23 = -3 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert11_23_oai := @OAI.UniversalTensorSquare.smallCert11_23_oai
