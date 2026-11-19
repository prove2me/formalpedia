-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_20
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:52:09.268403+00:00
-- url     : https://prove2.me/submissions/82f4819a-3507-41a3-a025-881fcb2ddf0a

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

lemma smallCert13_20_oai : solveCompact 13 (.full [4,3,2,2,2]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,2,2,2] (Equiv.refl (Fin 13)) smallB13_20 smallT13_20) smallFlag13_20 = 144 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_20_oai := @OAI.UniversalTensorSquare.smallCert13_20_oai
