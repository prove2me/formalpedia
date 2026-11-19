-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24639
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:31:42.074729+00:00
-- url     : https://prove2.me/submissions/62d0602a-bd45-49c8-a461-0a23cfe1a72b

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10108
import Theorems.Thm_OAI_UniversalTensorSquare_sg8526

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24639_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8526 sg10108

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24639_oai := @OAI.UniversalTensorSquare.sg24639_oai
