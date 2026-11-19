-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sgCert880
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:43:15.450857+00:00
-- url     : https://prove2.me/submissions/94d120b4-79e5-4e28-b291-56ec8ebaa1ed

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

lemma sgCert880_oai : solveCompact 10 (.full [8,1,1]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [8,1,1] (Equiv.refl (Fin 10)) sgB880 sgT880) sgFlag880 = -112 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sgCert880_oai := @OAI.UniversalTensorSquare.sgCert880_oai
