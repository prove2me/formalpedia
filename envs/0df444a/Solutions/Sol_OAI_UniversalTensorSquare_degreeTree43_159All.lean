-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_159All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:29:54.064971+00:00
-- url     : https://prove2.me/submissions/f5248e56-34e8-4f9e-8762-226026ca31ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_149All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_154All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_157All
import Theorems.Thm_OAI_UniversalTensorSquare_sg25611
import Theorems.Thm_OAI_UniversalTensorSquare_sg25676

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

lemma degreeTree43_158All : degreeTree43_158.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25676,degreeTree43_154All,degreeTree43_157All⟩

lemma degreeTree43_159All_oai : degreeTree43_159.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25611,degreeTree43_149All,degreeTree43_158All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_159All_oai := @OAI.UniversalTensorSquare.degreeTree43_159All_oai
