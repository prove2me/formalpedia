-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_17All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:00:21.536657+00:00
-- url     : https://prove2.me/submissions/8b5518d3-7ee8-4658-bf4e-d93c2a9a1b16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree39_15All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree39_16All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg295
import Theorems.Thm_OAI_UniversalTensorSquare_sg7036
import Theorems.Thm_OAI_UniversalTensorSquare_sg909

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

lemma sg1332 : RowSquare [6,1,1,1,1,1] [2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg909

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6373 : RowSquare [6,4,2,2,1,1,1,1,1] [4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg295 sg1332

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21932 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg6373 sg7036

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree39_17All_oai : degreeTree39_17.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21932,degreeTree39_15All,degreeTree39_16All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_17All_oai := @OAI.UniversalTensorSquare.degreeTree39_17All_oai
