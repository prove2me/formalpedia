-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg38751
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:44:07.41155+00:00
-- url     : https://prove2.me/submissions/51a4d68a-0bed-48cf-920e-0e2bdf26f335
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17475
import Theorems.Thm_OAI_UniversalTensorSquare_sg20506

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 95. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg38751_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17475

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg38751_oai := @OAI.UniversalTensorSquare.sg38751_oai
