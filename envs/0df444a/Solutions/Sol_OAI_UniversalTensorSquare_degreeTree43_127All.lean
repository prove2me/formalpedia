-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_127All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:45:09.491817+00:00
-- url     : https://prove2.me/submissions/ccdc27fe-191c-416d-b5b0-5669aca922d3

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg25290
import Theorems.Thm_OAI_UniversalTensorSquare_sg25291
import Theorems.Thm_OAI_UniversalTensorSquare_sg25292
import Theorems.Thm_OAI_UniversalTensorSquare_sg25293
import Theorems.Thm_OAI_UniversalTensorSquare_sg25294
import Theorems.Thm_OAI_UniversalTensorSquare_sg25295
import Theorems.Thm_OAI_UniversalTensorSquare_sg25296
import Theorems.Thm_OAI_UniversalTensorSquare_sg25297
import Theorems.Thm_OAI_UniversalTensorSquare_sg25298
import Theorems.Thm_OAI_UniversalTensorSquare_sg25299
import Theorems.Thm_OAI_UniversalTensorSquare_sg25301
import Theorems.Thm_OAI_UniversalTensorSquare_sg25302
import Theorems.Thm_OAI_UniversalTensorSquare_sg25303
import Theorems.Thm_OAI_UniversalTensorSquare_sg25304
import Theorems.Thm_OAI_UniversalTensorSquare_sg25305
import Theorems.Thm_OAI_UniversalTensorSquare_sg25306
import Theorems.Thm_OAI_UniversalTensorSquare_sg25307
import Theorems.Thm_OAI_UniversalTensorSquare_sg25308
import Theorems.Thm_OAI_UniversalTensorSquare_sg25309
import Theorems.Thm_OAI_UniversalTensorSquare_sg25310
import Theorems.Thm_OAI_UniversalTensorSquare_sg25311
import Theorems.Thm_OAI_UniversalTensorSquare_sg25312
import Theorems.Thm_OAI_UniversalTensorSquare_sg25313
import Theorems.Thm_OAI_UniversalTensorSquare_sg25314
import Theorems.Thm_OAI_UniversalTensorSquare_sg25315
import Theorems.Thm_OAI_UniversalTensorSquare_sg25316
import Theorems.Thm_OAI_UniversalTensorSquare_sg25317
import Theorems.Thm_OAI_UniversalTensorSquare_sg25318
import Theorems.Thm_OAI_UniversalTensorSquare_sg25319
import Theorems.Thm_OAI_UniversalTensorSquare_sg25320
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg9759

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8652 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1754

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25300 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9759

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

lemma degreeTree43_127All_oai : degreeTree43_127.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25305,⟨sg25297,⟨sg25293,⟨sg25291,⟨sg25290,True.intro,True.intro⟩,⟨sg25292,True.intro,True.intro⟩⟩,⟨sg25295,⟨sg25294,True.intro,True.intro⟩,⟨sg25296,True.intro,True.intro⟩⟩⟩,⟨sg25301,⟨sg25299,⟨sg25298,True.intro,True.intro⟩,⟨sg25300,True.intro,True.intro⟩⟩,⟨sg25303,⟨sg25302,True.intro,True.intro⟩,⟨sg25304,True.intro,True.intro⟩⟩⟩⟩,⟨sg25313,⟨sg25309,⟨sg25307,⟨sg25306,True.intro,True.intro⟩,⟨sg25308,True.intro,True.intro⟩⟩,⟨sg25311,⟨sg25310,True.intro,True.intro⟩,⟨sg25312,True.intro,True.intro⟩⟩⟩,⟨sg25317,⟨sg25315,⟨sg25314,True.intro,True.intro⟩,⟨sg25316,True.intro,True.intro⟩⟩,⟨sg25319,⟨sg25318,True.intro,True.intro⟩,⟨sg25320,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_127All_oai := @OAI.UniversalTensorSquare.degreeTree43_127All_oai
