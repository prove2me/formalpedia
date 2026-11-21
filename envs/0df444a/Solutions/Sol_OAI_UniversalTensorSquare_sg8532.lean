-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg8532
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:22:41.379701+00:00
-- url     : https://prove2.me/submissions/d1011f5f-e093-4370-83ad-11d4d352c2c1

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1328
import Theorems.Thm_OAI_UniversalTensorSquare_sg998
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8532_oai : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1328

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg8532_oai := @OAI.UniversalTensorSquare.sg8532_oai
