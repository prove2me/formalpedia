-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg14713
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:19:59.557172+00:00
-- url     : https://prove2.me/submissions/961d38be-a3d6-439b-b4c5-c35103f181e5

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2721
import Theorems.Thm_OAI_UniversalTensorSquare_sg2921

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14713_oai : RowSquare [6,5,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2721 sg2921

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg14713_oai := @OAI.UniversalTensorSquare.sg14713_oai
