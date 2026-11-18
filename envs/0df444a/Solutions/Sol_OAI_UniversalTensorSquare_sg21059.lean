-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21059
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:16:25.529893+00:00
-- url     : https://prove2.me/submissions/d12d231f-601e-437b-b7a9-7c05be500da9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg14713

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 51. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21059_oai : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14713

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21059_oai := @OAI.UniversalTensorSquare.sg21059_oai
