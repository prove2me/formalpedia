-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sgCert1065
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:31:44.686633+00:00
-- url     : https://prove2.me/submissions/8c50f148-4648-4f19-bf6b-453a333b26e0

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert1065_oai : solveCompact 10 (.full [4,3,3]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [4,3,3] (Equiv.refl (Fin 10)) sgB1065 sgT1065) sgFlag1065 = -4 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sgCert1065_oai := @OAI.UniversalTensorSquare.sgCert1065_oai
