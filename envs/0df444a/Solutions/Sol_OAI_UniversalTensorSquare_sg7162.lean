-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg7162
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:25:20.228933+00:00
-- url     : https://prove2.me/submissions/34c2bdb9-a32b-474e-aaf7-90a9990118fe

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg931
import Theorems.Thm_OAI_UniversalTensorSquare_sg999

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

lemma sg7162_oai : RowSquare [5,5,2,1,1,1,1,1,1,1,1] [6,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg931

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg7162_oai := @OAI.UniversalTensorSquare.sg7162_oai
