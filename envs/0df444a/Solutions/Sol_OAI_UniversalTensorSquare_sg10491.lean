-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg10491
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:33:51.124556+00:00
-- url     : https://prove2.me/submissions/e6739664-05bc-4122-a2a0-8680c69c69cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg890
import Theorems.Thm_OAI_UniversalTensorSquare_sg892

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1335 : RowSquare [6,1,1,1,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg890

lemma sg1358 : RowSquare [6,1,1,1,1,1] [5,5,1] := by
  exact rowSquare_join (by decide) sg0 sg892

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg10491_oai : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [8,7,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1335 sg1358

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg10491_oai := @OAI.UniversalTensorSquare.sg10491_oai
