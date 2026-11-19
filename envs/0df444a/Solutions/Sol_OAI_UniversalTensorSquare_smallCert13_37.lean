-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_37
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:53:18.313885+00:00
-- url     : https://prove2.me/submissions/80da1890-1924-4548-b8d5-a7759b35a274

import Mathlib
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

lemma smallCert13_37_oai : solveCompact 13 (.full [3,2,2,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,2,2,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_37 smallT13_37) smallFlag13_37 = -4 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_37_oai := @OAI.UniversalTensorSquare.smallCert13_37_oai
