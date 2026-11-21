-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_176All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:48:37.051012+00:00
-- url     : https://prove2.me/submissions/59b2d3e4-2068-4376-a192-fe070d17f432

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_174All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_175All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10098
import Theorems.Thm_OAI_UniversalTensorSquare_sg8564

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

lemma sg25887 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg8564 sg10098

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

lemma degreeTree43_176All_oai : degreeTree43_176.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25887,degreeTree43_174All,degreeTree43_175All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_176All_oai := @OAI.UniversalTensorSquare.degreeTree43_176All_oai
