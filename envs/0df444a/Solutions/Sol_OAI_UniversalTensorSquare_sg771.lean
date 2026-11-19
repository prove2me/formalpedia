-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg771
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:49:25.351045+00:00
-- url     : https://prove2.me/submissions/eff73c51-5d1a-452e-ba20-59aa5f927417

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg36

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg771_oai : RowSquare [3,3,1,1,1,1] [4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg36

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg771_oai := @OAI.UniversalTensorSquare.sg771_oai
