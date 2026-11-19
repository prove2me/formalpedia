-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4358
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T20:25:00.984704+00:00
-- url     : https://prove2.me/submissions/a95bbab5-4c9e-404d-9200-6816e80e238c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg67
import Theorems.Thm_OAI_UniversalTensorSquare_sg889

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4358_oai : RowSquare [8,2,2,2,1,1] [4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg889

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4358_oai := @OAI.UniversalTensorSquare.sg4358_oai
