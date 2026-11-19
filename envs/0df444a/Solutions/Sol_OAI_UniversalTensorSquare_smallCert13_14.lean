-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_14
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:48:55.957121+00:00
-- url     : https://prove2.me/submissions/9345175b-e4d8-45e7-b515-743280ca6b6e

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

lemma smallCert13_14_oai : solveChoices smallChoices13_14 (.full [4,4,3,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,4,3,1,1] (Equiv.refl (Fin 13)) smallB13_14 smallT13_14) smallFlag13_14 = 70 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_14_oai := @OAI.UniversalTensorSquare.smallCert13_14_oai
