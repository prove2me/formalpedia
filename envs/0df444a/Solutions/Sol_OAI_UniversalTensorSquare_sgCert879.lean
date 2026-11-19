-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sgCert879
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:43:04.321609+00:00
-- url     : https://prove2.me/submissions/b51cad92-a524-44c8-8570-dfba8c89907e

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

lemma sgCert879_oai : solveCompact 10 (.full [5,5]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [5,5] (Equiv.refl (Fin 10)) sgB879 sgT879) sgFlag879 = -8 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sgCert879_oai := @OAI.UniversalTensorSquare.sgCert879_oai
