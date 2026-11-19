-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sgCert833
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:42:07.150671+00:00
-- url     : https://prove2.me/submissions/e2c423ba-1680-47df-ba8d-ca468becfc7f

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

lemma sgCert833_oai : solveCompact 10 (.full [6,4]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [6,4] (Equiv.refl (Fin 10)) sgB833 sgT833) sgFlag833 = 6 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sgCert833_oai := @OAI.UniversalTensorSquare.sgCert833_oai
