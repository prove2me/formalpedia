-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_31
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:52:49.32316+00:00
-- url     : https://prove2.me/submissions/a76e0292-108d-48b8-b6ae-409a087bf567

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

lemma smallCert13_31_oai : solveChoices smallChoices13_31 (.full [3,3,2,2,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,2,2,1,1,1] (Equiv.refl (Fin 13)) smallB13_31 smallT13_31) smallFlag13_31 = -7 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_31_oai := @OAI.UniversalTensorSquare.smallCert13_31_oai
