-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg40783
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:10:26.438877+00:00
-- url     : https://prove2.me/submissions/1bc03575-96ae-460d-8e78-a6de919dc521
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg21047
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg2710

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

lemma sg4369 : RowSquare [8,3,1,1,1,1,1] [5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg2710

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15618 : RowSquare [7,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4369

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 100. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg40783_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,8,8,8,8,8,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15618 sg21047

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg40783_oai := @OAI.UniversalTensorSquare.sg40783_oai
