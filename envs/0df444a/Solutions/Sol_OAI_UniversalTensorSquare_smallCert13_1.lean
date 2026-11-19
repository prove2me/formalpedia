-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:48:38.975062+00:00
-- url     : https://prove2.me/submissions/a22e3057-2be2-45d5-9096-6bb76434d901

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US013

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_ChoiceCertificates13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choice certificates in degree thirteen. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_1_oai : solveChoices smallChoices13_1 (.full [6,2,2,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [6,2,2,1,1,1] (Equiv.refl (Fin 13)) smallB13_1 smallT13_1) smallFlag13_1 = 15 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_1_oai := @OAI.UniversalTensorSquare.smallCert13_1_oai
