-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg33938
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T04:04:54.784441+00:00
-- url     : https://prove2.me/submissions/42aae3d2-2e50-4942-8f56-2b1a9162b52a

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18285
import Theorems.Thm_OAI_UniversalTensorSquare_sg20355
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 83. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg33938_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,9,9,7,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18285 sg20355

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg33938_oai := @OAI.UniversalTensorSquare.sg33938_oai
