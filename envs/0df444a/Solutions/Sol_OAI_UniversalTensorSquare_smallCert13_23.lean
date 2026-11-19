-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_23
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:52:26.376228+00:00
-- url     : https://prove2.me/submissions/a807acdb-f305-4d32-a09f-fa714eda8dd4

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

lemma smallCert13_23_oai : solveCompact 13 (.full [4,3,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,3,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_23 smallT13_23) smallFlag13_23 = 8 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_23_oai := @OAI.UniversalTensorSquare.smallCert13_23_oai
