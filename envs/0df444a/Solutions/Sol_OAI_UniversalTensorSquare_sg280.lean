-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg280
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T14:07:54.423644+00:00
-- url     : https://prove2.me/submissions/55eba6ac-bf8b-49ad-b1d6-027048754a49

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg115

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

lemma sg280_oai : RowSquare [3,2,1,1,1] [4,3,1] := by
  exact rowSquare_join (by decide) sg0 sg115

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg280_oai := @OAI.UniversalTensorSquare.sg280_oai
