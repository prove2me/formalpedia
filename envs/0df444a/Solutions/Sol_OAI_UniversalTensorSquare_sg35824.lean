-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg35824
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T05:22:53.501178+00:00
-- url     : https://prove2.me/submissions/017ca34a-ed30-4a7d-b683-9bcfc33f4c89
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1762
import Theorems.Thm_OAI_UniversalTensorSquare_sg18914
import Theorems.Thm_OAI_UniversalTensorSquare_sg2707
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3599 : RowSquare [8,3,1,1,1,1] [5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg1762

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 36. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15182 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2707 sg3599

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 48. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19794 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15182

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 88. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg35824_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19794

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg35824_oai := @OAI.UniversalTensorSquare.sg35824_oai
