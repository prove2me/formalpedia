-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg460
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:29:09.489872+00:00
-- url     : https://prove2.me/submissions/1af0691c-54cd-4486-ad2c-12f0cd72f39c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg74

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 0. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg460_oai : RowSquare [3,2,1,1,1,1] [4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg74

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg460_oai := @OAI.UniversalTensorSquare.sg460_oai
