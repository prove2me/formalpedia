-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_29
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:52:38.178791+00:00
-- url     : https://prove2.me/submissions/367dcdf4-a4ec-4ad3-a253-3dbdd008bbaa

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US015

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

lemma smallCert13_29_oai : solveChoices smallChoices13_29 (.full [3,3,3,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,3,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_29 smallT13_29) smallFlag13_29 = 9 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_29_oai := @OAI.UniversalTensorSquare.smallCert13_29_oai
