-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg3065
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T22:42:07.871769+00:00
-- url     : https://prove2.me/submissions/50ce3235-45ee-4b62-87d6-ce1b72b0e736

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_trivial
import Theorems.Thm_OAI_UniversalTensorSquare_sg178

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLocalLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Local Leaves. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg206 : RowSquare [4,2,1] [7] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3065_oai : RowSquare [8,3,2,1] [8,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg206

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg3065_oai := @OAI.UniversalTensorSquare.sg3065_oai
