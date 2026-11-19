-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sgCert792
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:38:08.118571+00:00
-- url     : https://prove2.me/submissions/26ad5a00-c655-4c46-b46b-867f603fa51d

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

lemma sgCert792_oai : solveCompact 10 (.full [5,5]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [5,5] (Equiv.refl (Fin 10)) sgB792 sgT792) sgFlag792 = -14 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sgCert792_oai := @OAI.UniversalTensorSquare.sgCert792_oai
