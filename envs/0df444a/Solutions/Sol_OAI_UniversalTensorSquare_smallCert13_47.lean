-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_47
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:56:23.399101+00:00
-- url     : https://prove2.me/submissions/07f2e321-5052-4cb7-bad4-38eb05087aef

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US019

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_47_oai : solveChoices smallChoices13_47 (.full [2,2,2,2,2,2,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [2,2,2,2,2,2,1] (Equiv.refl (Fin 13)) smallB13_47 smallT13_47) smallFlag13_47 = -1 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_47_oai := @OAI.UniversalTensorSquare.smallCert13_47_oai
