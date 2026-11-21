-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg29232
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T16:16:16.908694+00:00
-- url     : https://prove2.me/submissions/a22afc4e-efd8-4e91-9e4e-1042bcd15d74

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg15533
import Theorems.Thm_OAI_UniversalTensorSquare_sg2228

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 71. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29232_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2228 sg15533

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg29232_oai := @OAI.UniversalTensorSquare.sg29232_oai
