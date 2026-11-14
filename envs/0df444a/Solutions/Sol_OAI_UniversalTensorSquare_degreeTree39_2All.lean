-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_2All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T01:52:49.293327+00:00
-- url     : https://prove2.me/submissions/b04258b3-51f6-43ee-abe2-a571aa4ba7cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree39_0All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree39_1All
import Theorems.Thm_OAI_UniversalTensorSquare_sg21700

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

lemma degreeTree39_2All_oai : degreeTree39_2.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21700,degreeTree39_0All,degreeTree39_1All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_2All_oai := @OAI.UniversalTensorSquare.degreeTree39_2All_oai
