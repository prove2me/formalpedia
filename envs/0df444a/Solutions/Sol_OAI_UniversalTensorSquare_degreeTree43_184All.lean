-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_184All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:51:22.645701+00:00
-- url     : https://prove2.me/submissions/10408130-47f3-4778-bfa1-e3ef21dbcb6c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg26000
import Theorems.Thm_OAI_UniversalTensorSquare_sg26001
import Theorems.Thm_OAI_UniversalTensorSquare_sg26002
import Theorems.Thm_OAI_UniversalTensorSquare_sg26003
import Theorems.Thm_OAI_UniversalTensorSquare_sg26004
import Theorems.Thm_OAI_UniversalTensorSquare_sg26005
import Theorems.Thm_OAI_UniversalTensorSquare_sg26007
import Theorems.Thm_OAI_UniversalTensorSquare_sg26008
import Theorems.Thm_OAI_UniversalTensorSquare_sg26009
import Theorems.Thm_OAI_UniversalTensorSquare_sg26010
import Theorems.Thm_OAI_UniversalTensorSquare_sg26011
import Theorems.Thm_OAI_UniversalTensorSquare_sg26012
import Theorems.Thm_OAI_UniversalTensorSquare_sg26013
import Theorems.Thm_OAI_UniversalTensorSquare_sg26014
import Theorems.Thm_OAI_UniversalTensorSquare_sg26015
import Theorems.Thm_OAI_UniversalTensorSquare_sg8798
import Theorems.Thm_OAI_UniversalTensorSquare_sg9220

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

lemma sg26006 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9220

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

lemma degreeTree43_184All_oai : degreeTree43_184.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26008,⟨sg26004,⟨sg26002,⟨sg26001,⟨sg26000,True.intro,True.intro⟩,True.intro⟩,⟨sg26003,True.intro,True.intro⟩⟩,⟨sg26006,⟨sg26005,True.intro,True.intro⟩,⟨sg26007,True.intro,True.intro⟩⟩⟩,⟨sg26012,⟨sg26010,⟨sg26009,True.intro,True.intro⟩,⟨sg26011,True.intro,True.intro⟩⟩,⟨sg26014,⟨sg26013,True.intro,True.intro⟩,⟨sg26015,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_184All_oai := @OAI.UniversalTensorSquare.degreeTree43_184All_oai
