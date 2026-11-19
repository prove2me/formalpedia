-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg8011
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:06:20.734146+00:00
-- url     : https://prove2.me/submissions/32dd6321-3fc2-4e12-81d2-e4faaf3897d9

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg891
import Theorems.Thm_OAI_UniversalTensorSquare_sg942
import Definitions.Def_OAIQ259US001

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8011_oai : RowSquare [10,3,3,2,1,1] [4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg942 sg891

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg8011_oai := @OAI.UniversalTensorSquare.sg8011_oai
