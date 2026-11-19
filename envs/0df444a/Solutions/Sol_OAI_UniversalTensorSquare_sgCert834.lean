-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sgCert834
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:42:12.984063+00:00
-- url     : https://prove2.me/submissions/7d772a1d-63c3-431f-9140-6a8890557f33

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

lemma sgCert834_oai : solveCompact 10 (.full [5,5]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [5,5] (Equiv.refl (Fin 10)) sgB834 sgT834) sgFlag834 = 32 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sgCert834_oai := @OAI.UniversalTensorSquare.sgCert834_oai
