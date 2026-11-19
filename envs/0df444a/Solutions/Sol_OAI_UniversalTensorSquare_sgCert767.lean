-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sgCert767
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:38:02.317214+00:00
-- url     : https://prove2.me/submissions/36393eb8-a22a-4c46-beed-cdf7a3ebbe7e

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

lemma sgCert767_oai : solveCompact 10 (.full [4,4,2]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB767 sgT767) sgFlag767 = 10 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sgCert767_oai := @OAI.UniversalTensorSquare.sgCert767_oai
