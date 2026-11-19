-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_36
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:53:12.609107+00:00
-- url     : https://prove2.me/submissions/4a404b82-2ea6-4540-9ae4-7ee1c7a44de3

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_36_oai : solveCompact 13 (.full [3,2,2,2,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,2,2,2,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_36 smallT13_36) smallFlag13_36 = -7 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_36_oai := @OAI.UniversalTensorSquare.smallCert13_36_oai
