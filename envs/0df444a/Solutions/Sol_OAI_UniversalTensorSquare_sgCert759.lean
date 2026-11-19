-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sgCert759
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:37:51.033465+00:00
-- url     : https://prove2.me/submissions/9177a5a4-d856-4e4c-8b33-7b890ce4ea00

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

lemma sgCert759_oai : solveCompact 10 (.full [5,5]) (.full [3,2,2,2,1]) (.full [3,2,2,2,1])
    (certificateEdges [3,2,2,2,1] [3,2,2,2,1] [5,5] (Equiv.refl (Fin 10)) sgB759 sgT759) sgFlag759 = -9 := by
  decide +kernel

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sgCert759_oai := @OAI.UniversalTensorSquare.sgCert759_oai
