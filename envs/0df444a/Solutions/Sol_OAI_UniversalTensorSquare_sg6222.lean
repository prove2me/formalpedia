-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6222
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:57:27.30067+00:00
-- url     : https://prove2.me/submissions/2de5e9f0-d3b7-416d-b2d6-db4140853d89

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg595
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6222_oai : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg595 sg998

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6222_oai := @OAI.UniversalTensorSquare.sg6222_oai
