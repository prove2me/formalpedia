-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_17
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:51:52.23248+00:00
-- url     : https://prove2.me/submissions/5d990c9d-5e7a-4e86-a3db-9fb2cfe4592e

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

lemma smallCert13_17_oai : solveChoices smallChoices13_17 (.full [4,4,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,4,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_17 smallT13_17) smallFlag13_17 = -14 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_17_oai := @OAI.UniversalTensorSquare.smallCert13_17_oai
