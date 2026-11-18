-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg36963
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T13:48:56.64904+00:00
-- url     : https://prove2.me/submissions/bdd612d7-8abd-4e75-9bf5-9394d744e79c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18910
import Theorems.Thm_OAI_UniversalTensorSquare_sg19865

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 91. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg36963_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,7,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19865

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg36963_oai := @OAI.UniversalTensorSquare.sg36963_oai
