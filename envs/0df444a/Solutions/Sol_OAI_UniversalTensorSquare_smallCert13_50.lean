-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:58:49.306249+00:00
-- url     : https://prove2.me/submissions/616376b4-753a-470f-bbf6-d3627ceb43e7

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US020

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

lemma smallCert13_50_oai : solveChoices smallChoices13_50 (.full [2,2,1,1,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [2,2,1,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_50 smallT13_50) smallFlag13_50 = 12 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_50_oai := @OAI.UniversalTensorSquare.smallCert13_50_oai
