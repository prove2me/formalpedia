-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:55:36.665386+00:00
-- url     : https://prove2.me/submissions/515c2392-a112-4f6c-aaff-3b4650f2d71e

import Mathlib
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_4_oai : solveCompact 13 (.full [5,4,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,4,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_4 smallT13_4) smallFlag13_4 = -13 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_4_oai := @OAI.UniversalTensorSquare.smallCert13_4_oai
