-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sgCert982
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:48:08.159935+00:00
-- url     : https://prove2.me/submissions/36bbf90b-95cf-4e29-ac8d-95dce0548168

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

lemma sgCert982_oai : solveCompact 10 (.full [5,5]) (.full [3,2,2,2,1]) (.full [3,2,2,2,1])
    (certificateEdges [3,2,2,2,1] [3,2,2,2,1] [5,5] (Equiv.refl (Fin 10)) sgB982 sgT982) sgFlag982 = 99 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sgCert982_oai := @OAI.UniversalTensorSquare.sgCert982_oai
