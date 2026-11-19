-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:53:06.947115+00:00
-- url     : https://prove2.me/submissions/91f8392d-6851-4515-b1d9-df8846f8ec04

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US018

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_35_oai : solveChoices smallChoices13_35 (.full [3,2,2,2,2,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,2,2,2,2,1,1] (Equiv.refl (Fin 13)) smallB13_35 smallT13_35) smallFlag13_35 = 16 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_35_oai := @OAI.UniversalTensorSquare.smallCert13_35_oai
