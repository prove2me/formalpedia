-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_45
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:56:11.952598+00:00
-- url     : https://prove2.me/submissions/c03d4af6-019f-4160-9d45-96dbe1f19932

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

lemma smallCert13_45_oai : solveChoices smallChoices13_45 (.full [3,3,3,2,2]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,3,2,2] (Equiv.refl (Fin 13)) smallB13_45 smallT13_45) smallFlag13_45 = -4 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_45_oai := @OAI.UniversalTensorSquare.smallCert13_45_oai
