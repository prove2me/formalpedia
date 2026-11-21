-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_183All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:08:38.353578+00:00
-- url     : https://prove2.me/submissions/bc7e8f8e-0f1e-443d-922d-5af99a6844ac

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_167All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_170All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_171All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_182All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg11468
import Theorems.Thm_OAI_UniversalTensorSquare_sg25805
import Theorems.Thm_OAI_UniversalTensorSquare_sg25870
import Theorems.Thm_OAI_UniversalTensorSquare_sg6942

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 63. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25838 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6942 sg11468

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree43_172All : degreeTree43_172.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25838,degreeTree43_170All,degreeTree43_171All⟩

lemma degreeTree43_173All : degreeTree43_173.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25805,degreeTree43_167All,degreeTree43_172All⟩

lemma degreeTree43_183All_oai : degreeTree43_183.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25870,degreeTree43_173All,degreeTree43_182All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_183All_oai := @OAI.UniversalTensorSquare.degreeTree43_183All_oai
