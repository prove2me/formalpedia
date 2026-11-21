-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg4022
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:31:29.65769+00:00
-- url     : https://prove2.me/submissions/cfe2975d-f151-4b99-bf2d-ef30f4db70b3

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg12
import Theorems.Thm_OAI_UniversalTensorSquare_sg120
import Theorems.Thm_OAI_UniversalTensorSquare_sg32

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 0. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg501 : RowSquare [3,3,1,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12 sg32

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4022_oai : RowSquare [5,5,2,2,2] [5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg120 sg501

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg4022_oai := @OAI.UniversalTensorSquare.sg4022_oai
