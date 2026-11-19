-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_19
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:51:57.758725+00:00
-- url     : https://prove2.me/submissions/332d7a13-d436-4c13-aa38-f666f2207024

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US015

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

lemma smallCert13_19_oai : solveChoices smallChoices13_19 (.full [4,3,3,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,3,1,1,1] (Equiv.refl (Fin 13)) smallB13_19 smallT13_19) smallFlag13_19 = -22 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_19_oai := @OAI.UniversalTensorSquare.smallCert13_19_oai
