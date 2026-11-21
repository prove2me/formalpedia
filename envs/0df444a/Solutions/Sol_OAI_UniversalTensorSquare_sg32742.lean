-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg32742
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T03:53:08.971205+00:00
-- url     : https://prove2.me/submissions/5b0f8dd4-1f8e-4929-a66d-ddfa6e44235b

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17231
import Theorems.Thm_OAI_UniversalTensorSquare_sg20526

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 80. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg32742_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,9,9,8,8,8,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17231

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg32742_oai := @OAI.UniversalTensorSquare.sg32742_oai
