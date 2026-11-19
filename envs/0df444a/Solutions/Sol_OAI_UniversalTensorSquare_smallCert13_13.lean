-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:48:49.997507+00:00
-- url     : https://prove2.me/submissions/b6561488-eed9-45c4-becd-60c67c284eb3

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

lemma smallCert13_13_oai : solveChoices smallChoices13_13 (.full [5,1,1,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_13 smallT13_13) smallFlag13_13 = -16 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_13_oai := @OAI.UniversalTensorSquare.smallCert13_13_oai
