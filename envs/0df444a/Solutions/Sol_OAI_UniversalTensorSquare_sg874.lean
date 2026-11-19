-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg874
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:28:20.337693+00:00
-- url     : https://prove2.me/submissions/9d7582fb-dc0a-43d8-b6ed-0a2846053146

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert874

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg874_oai : RowSquare [4,3,3] [2,2,2,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,3,1]) (ts := [7,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB874 sgT874 sgFlag874
  change solveCompact 10 (.full [7,3]) (.full [3,3,3,1]) (.full [3,3,3,1])
    (certificateEdges [3,3,3,1] [3,3,3,1] [7,3] (Equiv.refl (Fin 10)) sgB874 sgT874) sgFlag874 ≠ 0
  rw [sgCert874]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg874_oai := @OAI.UniversalTensorSquare.sg874_oai
