-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:48:44.530689+00:00
-- url     : https://prove2.me/submissions/652ad00d-592b-4ea7-a62f-74d40ba65cd4

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US014

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

lemma smallCert13_10_oai : solveChoices smallChoices13_10 (.full [5,2,2,2,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,2,2,2,1,1] (Equiv.refl (Fin 13)) smallB13_10 smallT13_10) smallFlag13_10 = -1 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_10_oai := @OAI.UniversalTensorSquare.smallCert13_10_oai
