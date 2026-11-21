-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12509
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:11:52.916218+00:00
-- url     : https://prove2.me/submissions/02263d2c-9c0c-4b21-abeb-7b07bc4e5e35

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1891
import Theorems.Thm_OAI_UniversalTensorSquare_sg2407

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12509_oai : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg2407

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12509_oai := @OAI.UniversalTensorSquare.sg12509_oai
