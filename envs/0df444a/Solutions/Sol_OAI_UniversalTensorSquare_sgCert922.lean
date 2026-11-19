-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sgCert922
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:47:04.876703+00:00
-- url     : https://prove2.me/submissions/3f2d1481-8351-4d10-987c-5a6cf77e7e20

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

lemma sgCert922_oai : solveCompact 10 (.full [4,4,2]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
    (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB922 sgT922) sgFlag922 = 4 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sgCert922_oai := @OAI.UniversalTensorSquare.sgCert922_oai
