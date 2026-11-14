-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg1177
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T20:46:23.508203+00:00
-- url     : https://prove2.me/submissions/2a2d2bf7-bf3a-4659-ad15-257d87a17981

import Mathlib
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_trivial

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLocalLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Local Leaves. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1177_oai : RowSquare [3,3,1,1,1,1,1] [11] := by
  exact rowSquare_trivial _ (by decide)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg1177_oai := @OAI.UniversalTensorSquare.sg1177_oai
