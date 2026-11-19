-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sgCert579
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:37:05.550221+00:00
-- url     : https://prove2.me/submissions/d21ac00f-d9ce-48eb-8343-005981f559a5

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert579_oai : solveCompact 9 (.full [6,3]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [6,3] (Equiv.refl (Fin 9)) sgB579 sgT579) sgFlag579 = 18 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sgCert579_oai := @OAI.UniversalTensorSquare.sgCert579_oai
