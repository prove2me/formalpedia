-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sgCert874
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:42:41.208806+00:00
-- url     : https://prove2.me/submissions/6424b0cb-7c0a-4ab5-81b8-322d909bb16a

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

lemma sgCert874_oai : solveCompact 10 (.full [7,3]) (.full [3,3,3,1]) (.full [3,3,3,1])
    (certificateEdges [3,3,3,1] [3,3,3,1] [7,3] (Equiv.refl (Fin 10)) sgB874 sgT874) sgFlag874 = 45 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sgCert874_oai := @OAI.UniversalTensorSquare.sgCert874_oai
