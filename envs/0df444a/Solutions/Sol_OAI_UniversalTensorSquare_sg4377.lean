-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4377
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:25:12.607207+00:00
-- url     : https://prove2.me/submissions/b4c7ffcf-3e40-4ff2-aed1-4b07fa46d834

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg74
import Theorems.Thm_OAI_UniversalTensorSquare_sg890
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4377_oai : RowSquare [8,3,2,1,1,1] [3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg890

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4377_oai := @OAI.UniversalTensorSquare.sg4377_oai
