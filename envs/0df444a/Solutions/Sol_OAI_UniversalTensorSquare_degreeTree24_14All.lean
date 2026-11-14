-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree24_14All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T20:54:55.620204+00:00
-- url     : https://prove2.me/submissions/5cb2127a-75c2-41a2-b354-dc0dad78bbf1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree24_13All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree24_2All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree24_5All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10900
import Theorems.Thm_OAI_UniversalTensorSquare_sg11963

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11520 : RowSquare [7,6,2,2,2,2,1,1] [5,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10900

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 28. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11902 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11520

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree24_6All : degreeTree24_6.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg11902,degreeTree24_2All,degreeTree24_5All⟩

lemma degreeTree24_14All_oai : degreeTree24_14.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg11963,degreeTree24_6All,degreeTree24_13All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree24_14All_oai := @OAI.UniversalTensorSquare.degreeTree24_14All_oai
