-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg36530
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T13:21:18.085308+00:00
-- url     : https://prove2.me/submissions/675cf4da-b23c-455a-93be-ba139bbf6930

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18946
import Theorems.Thm_OAI_UniversalTensorSquare_sg19624

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg36530_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,6,6,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg19624 sg18946

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg36530_oai := @OAI.UniversalTensorSquare.sg36530_oai
