-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:48:33.280195+00:00
-- url     : https://prove2.me/submissions/f31f1b2d-876a-4f97-942f-66dfadcfce28

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

lemma smallCert13_0_oai : solveChoices smallChoices13_0 (.full [7,1,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [7,1,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_0 smallT13_0) smallFlag13_0 = 116 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_0_oai := @OAI.UniversalTensorSquare.smallCert13_0_oai
