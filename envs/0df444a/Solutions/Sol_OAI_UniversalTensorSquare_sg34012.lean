-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg34012
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T10:43:34.919858+00:00
-- url     : https://prove2.me/submissions/e7f2315e-5223-4201-abbc-1636946c35be

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg17213
import Theorems.Thm_OAI_UniversalTensorSquare_sg20538
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 83. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg34012_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,11,9,9,9,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20538 sg17213

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg34012_oai := @OAI.UniversalTensorSquare.sg34012_oai
