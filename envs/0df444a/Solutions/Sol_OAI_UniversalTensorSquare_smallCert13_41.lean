-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_41
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:55:48.637293+00:00
-- url     : https://prove2.me/submissions/b243b430-cf31-47c5-a917-341bec9cd411

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US014

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 10. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_41_oai : solveChoices smallChoices13_41 (.full [2,1,1,1,1,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [2,1,1,1,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_41 smallT13_41) smallFlag13_41 = 48 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_41_oai := @OAI.UniversalTensorSquare.smallCert13_41_oai
