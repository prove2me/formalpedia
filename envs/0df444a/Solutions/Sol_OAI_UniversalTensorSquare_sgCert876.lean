-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sgCert876
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:42:46.897097+00:00
-- url     : https://prove2.me/submissions/acfede4a-4d99-43c2-9ec4-eabd4b2bafe1

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

lemma sgCert876_oai : solveCompact 10 (.full [8,1,1]) (.full [3,3,3,1]) (.full [3,3,3,1])
    (certificateEdges [3,3,3,1] [3,3,3,1] [8,1,1] (Equiv.refl (Fin 10)) sgB876 sgT876) sgFlag876 = 60 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sgCert876_oai := @OAI.UniversalTensorSquare.sgCert876_oai
