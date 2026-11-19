-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12135
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:47:04.222628+00:00
-- url     : https://prove2.me/submissions/37dad6e9-6a4e-4763-9695-b03febee5852

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1202
import Theorems.Thm_OAI_UniversalTensorSquare_sg2048

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 28. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12135_oai : RowSquare [8,6,2,2,2,2,1,1] [7,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2048

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12135_oai := @OAI.UniversalTensorSquare.sg12135_oai
