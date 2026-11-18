-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg18911
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:02:33.141906+00:00
-- url     : https://prove2.me/submissions/49b336d4-c99d-4d02-a54d-92af8913cf27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg6469

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 45. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18911_oai : RowSquare [7,6,4,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1754 sg6469

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg18911_oai := @OAI.UniversalTensorSquare.sg18911_oai
