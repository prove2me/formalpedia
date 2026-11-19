-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_48
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:56:28.867869+00:00
-- url     : https://prove2.me/submissions/ae05dfc5-2d19-425e-8633-a87a1ee1bbe7

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US019

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_48_oai : solveChoices smallChoices13_48 (.full [2,2,2,2,2,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [2,2,2,2,2,1,1,1] (Equiv.refl (Fin 13)) smallB13_48 smallT13_48) smallFlag13_48 = -10 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_48_oai := @OAI.UniversalTensorSquare.smallCert13_48_oai
