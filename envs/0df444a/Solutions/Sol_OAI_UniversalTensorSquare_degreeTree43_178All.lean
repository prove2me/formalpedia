-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_178All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T14:19:48.854438+00:00
-- url     : https://prove2.me/submissions/f4216cb8-f4a4-4bc9-9288-c2f0da2a9b30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_176All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_177All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10274
import Theorems.Thm_OAI_UniversalTensorSquare_sg8430

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

lemma sg25903 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10274

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

lemma degreeTree43_178All_oai : degreeTree43_178.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25903,degreeTree43_176All,degreeTree43_177All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_178All_oai := @OAI.UniversalTensorSquare.degreeTree43_178All_oai
