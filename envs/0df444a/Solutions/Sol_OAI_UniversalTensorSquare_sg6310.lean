-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6310
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:58:12.624618+00:00
-- url     : https://prove2.me/submissions/b34655f2-7904-4169-b499-acb425438dd7

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg587
import Theorems.Thm_OAI_UniversalTensorSquare_sg841
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

lemma sg6310_oai : RowSquare [5,5,2,2,1,1,1,1,1] [4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg841

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6310_oai := @OAI.UniversalTensorSquare.sg6310_oai
