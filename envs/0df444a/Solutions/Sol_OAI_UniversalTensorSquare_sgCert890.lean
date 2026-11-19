-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sgCert890
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:43:32.208988+00:00
-- url     : https://prove2.me/submissions/cf93bd83-41c2-4af6-98ca-56017b72eba4

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert890_oai : solveCompact 10 (.full [7,3]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [7,3] (Equiv.refl (Fin 10)) sgB890 sgT890) sgFlag890 = -48 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sgCert890_oai := @OAI.UniversalTensorSquare.sgCert890_oai
