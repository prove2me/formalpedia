-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_15
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:51:41.032781+00:00
-- url     : https://prove2.me/submissions/f17dfecb-450c-4239-a77c-15f2ca71d921

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US014

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_15_oai : solveChoices smallChoices13_15 (.full [4,4,2,2,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,4,2,2,1] (Equiv.refl (Fin 13)) smallB13_15 smallT13_15) smallFlag13_15 = -1 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_15_oai := @OAI.UniversalTensorSquare.smallCert13_15_oai
