-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg10307
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T22:15:59.969316+00:00
-- url     : https://prove2.me/submissions/b11e6c1e-7be9-4b8a-a4c9-c1a3988220ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1337
import Theorems.Thm_OAI_UniversalTensorSquare_sg1340

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10307_oai : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg1337 sg1340

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg10307_oai := @OAI.UniversalTensorSquare.sg10307_oai
