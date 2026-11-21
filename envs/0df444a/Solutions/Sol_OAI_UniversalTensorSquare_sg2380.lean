-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg2380
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:43:25.22873+00:00
-- url     : https://prove2.me/submissions/440a6477-aa1c-4b1e-b7c8-6f621ea1083c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg5

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2380_oai : RowSquare [8,2,1,1,1] [4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg1001

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg2380_oai := @OAI.UniversalTensorSquare.sg2380_oai
