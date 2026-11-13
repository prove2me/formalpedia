-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_84All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:32:17.552364+00:00
-- url     : https://prove2.me/submissions/25fce6b0-abce-4d97-98c7-eff7619b9350
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree39_80All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree39_83All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg6157
import Theorems.Thm_OAI_UniversalTensorSquare_sg7606

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 55. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg22891 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,5,5,5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6157 sg7606

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

lemma degreeTree39_84All_oai : degreeTree39_84.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22891,degreeTree39_80All,degreeTree39_83All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_84All_oai := @OAI.UniversalTensorSquare.degreeTree39_84All_oai
