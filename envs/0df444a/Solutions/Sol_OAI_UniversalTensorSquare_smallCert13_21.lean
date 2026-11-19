-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_21
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:52:14.954195+00:00
-- url     : https://prove2.me/submissions/63c89d8a-87b4-42e1-ab41-e5726c656d23

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_21_oai : solveCompact 13 (.full [4,3,2,2,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,2,2,1,1] (Equiv.refl (Fin 13)) smallB13_21 smallT13_21) smallFlag13_21 = -24 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_21_oai := @OAI.UniversalTensorSquare.smallCert13_21_oai
