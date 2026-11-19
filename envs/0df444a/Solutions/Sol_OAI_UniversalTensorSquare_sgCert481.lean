-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sgCert481
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:33:31.952816+00:00
-- url     : https://prove2.me/submissions/7bd30792-d320-4b43-9530-f01d35a39565

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert481_oai : solveCompact 9 (.full [5,4]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [5,4] (Equiv.refl (Fin 9)) sgB481 sgT481) sgFlag481 = -12 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sgCert481_oai := @OAI.UniversalTensorSquare.sgCert481_oai
