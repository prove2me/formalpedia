-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg1683
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:37:58.006592+00:00
-- url     : https://prove2.me/submissions/a9881335-c252-42d2-bc6e-d67de525dc0e

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg54
import Theorems.Thm_OAI_UniversalTensorSquare_sg82

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1683_oai : RowSquare [5,3,2,1,1] [2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg82 sg54

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg1683_oai := @OAI.UniversalTensorSquare.sg1683_oai
