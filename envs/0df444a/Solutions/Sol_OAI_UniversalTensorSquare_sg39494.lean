-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg39494
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T14:19:13.662033+00:00
-- url     : https://prove2.me/submissions/eabbb588-2154-4842-8a41-aeda5748f2d6

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18074
import Theorems.Thm_OAI_UniversalTensorSquare_sg20498
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 97. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg39494_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,8,8,7,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18074

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg39494_oai := @OAI.UniversalTensorSquare.sg39494_oai
