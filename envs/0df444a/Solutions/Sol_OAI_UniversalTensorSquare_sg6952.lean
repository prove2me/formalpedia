-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6952
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:17:35.623553+00:00
-- url     : https://prove2.me/submissions/fc8d1ceb-c1e2-479a-b474-46cf21aa0e13

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg1007

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6952_oai : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg1001 sg1007

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6952_oai := @OAI.UniversalTensorSquare.sg6952_oai
