-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallCert13_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:52:03.714166+00:00
-- url     : https://prove2.me/submissions/997c3817-16f6-4015-a52b-2fb80e1e4584

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US015

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

lemma smallCert13_2_oai : solveChoices smallChoices13_2 (.full [6,2,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [6,2,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_2 smallT13_2) smallFlag13_2 = -9 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallCert13_2_oai := @OAI.UniversalTensorSquare.smallCert13_2_oai
