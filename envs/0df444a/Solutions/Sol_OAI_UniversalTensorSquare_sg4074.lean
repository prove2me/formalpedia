-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4074
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:11:28.413795+00:00
-- url     : https://prove2.me/submissions/2bb14179-3340-4fe4-bf20-99b719c7527c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg248
import Theorems.Thm_OAI_UniversalTensorSquare_sg339

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4074_oai : RowSquare [6,4,2,2,1,1] [3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg339 sg248

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4074_oai := @OAI.UniversalTensorSquare.sg4074_oai
