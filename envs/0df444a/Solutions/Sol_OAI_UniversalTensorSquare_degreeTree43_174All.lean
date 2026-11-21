-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_174All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:59:03.89893+00:00
-- url     : https://prove2.me/submissions/2eadd6a0-a0c8-4497-974e-6e99a6873150

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Theorems.Thm_OAI_UniversalTensorSquare_sg25871
import Theorems.Thm_OAI_UniversalTensorSquare_sg25872
import Theorems.Thm_OAI_UniversalTensorSquare_sg25873
import Theorems.Thm_OAI_UniversalTensorSquare_sg25874
import Theorems.Thm_OAI_UniversalTensorSquare_sg25875
import Theorems.Thm_OAI_UniversalTensorSquare_sg25876
import Theorems.Thm_OAI_UniversalTensorSquare_sg25877
import Theorems.Thm_OAI_UniversalTensorSquare_sg25878
import Theorems.Thm_OAI_UniversalTensorSquare_sg25879
import Theorems.Thm_OAI_UniversalTensorSquare_sg25880
import Theorems.Thm_OAI_UniversalTensorSquare_sg25881
import Theorems.Thm_OAI_UniversalTensorSquare_sg25882
import Theorems.Thm_OAI_UniversalTensorSquare_sg25883
import Theorems.Thm_OAI_UniversalTensorSquare_sg25884
import Theorems.Thm_OAI_UniversalTensorSquare_sg25885
import Theorems.Thm_OAI_UniversalTensorSquare_sg25886

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

lemma degreeTree43_174All_oai : degreeTree43_174.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25879,⟨sg25875,⟨sg25873,⟨sg25872,⟨sg25871,True.intro,True.intro⟩,True.intro⟩,⟨sg25874,True.intro,True.intro⟩⟩,⟨sg25877,⟨sg25876,True.intro,True.intro⟩,⟨sg25878,True.intro,True.intro⟩⟩⟩,⟨sg25883,⟨sg25881,⟨sg25880,True.intro,True.intro⟩,⟨sg25882,True.intro,True.intro⟩⟩,⟨sg25885,⟨sg25884,True.intro,True.intro⟩,⟨sg25886,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_174All_oai := @OAI.UniversalTensorSquare.degreeTree43_174All_oai
