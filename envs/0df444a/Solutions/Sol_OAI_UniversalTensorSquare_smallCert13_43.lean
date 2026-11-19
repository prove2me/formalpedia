-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_43
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:55:59.732552+00:00
-- url     : https://prove2.me/submissions/36e08498-2aed-442f-8bbd-9a71950ff4f4

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US018

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 10. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_43_oai : solveChoices smallChoices13_43 (.full [4,3,3,3]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,3,3] (Equiv.refl (Fin 13)) smallB13_43 smallT13_43) smallFlag13_43 = 6 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_43_oai := @OAI.UniversalTensorSquare.smallCert13_43_oai
