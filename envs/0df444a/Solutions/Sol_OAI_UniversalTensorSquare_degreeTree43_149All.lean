-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_149All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:04:16.952986+00:00
-- url     : https://prove2.me/submissions/92513296-0f6d-4f8f-8905-e57d4e00d00f

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_143All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_144All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_148All
import Theorems.Thm_OAI_UniversalTensorSquare_sg25515
import Theorems.Thm_OAI_UniversalTensorSquare_sg25547

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

lemma degreeTree43_145All : degreeTree43_145.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25515,degreeTree43_143All,degreeTree43_144All⟩

lemma degreeTree43_149All_oai : degreeTree43_149.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25547,degreeTree43_145All,degreeTree43_148All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_149All_oai := @OAI.UniversalTensorSquare.degreeTree43_149All_oai
