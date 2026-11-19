-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg778
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:52:49.532247+00:00
-- url     : https://prove2.me/submissions/6a6b8b88-fd32-45f8-9fb4-7539336a4cd9

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg35

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg778_oai : RowSquare [3,3,1,1,1,1] [5,3,2] := by
  exact rowSquare_join (by decide) sg34 sg35

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg778_oai := @OAI.UniversalTensorSquare.sg778_oai
