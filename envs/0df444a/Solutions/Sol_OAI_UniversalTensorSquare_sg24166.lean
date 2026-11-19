-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg24166
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T01:20:00.391267+00:00
-- url     : https://prove2.me/submissions/14b444ff-30af-41b1-b3c2-29d01a5c883c

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg9752

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24166_oai : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9752

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg24166_oai := @OAI.UniversalTensorSquare.sg24166_oai
