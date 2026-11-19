-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_42
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:55:54.225614+00:00
-- url     : https://prove2.me/submissions/f323abbe-2c7c-4f36-8ea2-7d5982ba87b6

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US017

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

lemma smallCert13_42_oai : solveChoices smallChoices13_42 (.full [4,4,3,2]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,4,3,2] (Equiv.refl (Fin 13)) smallB13_42 smallT13_42) smallFlag13_42 = 4 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_42_oai := @OAI.UniversalTensorSquare.smallCert13_42_oai
