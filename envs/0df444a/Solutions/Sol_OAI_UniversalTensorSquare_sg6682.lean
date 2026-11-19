-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6682
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:06:18.388652+00:00
-- url     : https://prove2.me/submissions/94dcdba4-f32c-4dbc-abf8-d36006a1270d

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1033
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert949 : solveCompact 10 (.full [5,3,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [5,3,2] (Equiv.refl (Fin 10)) sgB949 sgT949) sgFlag949 = 4 := by
  decide +kernel

lemma sg949 : RowSquare [5,2,2,1] [3,3,2,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,3,1,1,1]) (ts := [5,3,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB949 sgT949 sgFlag949
  change solveCompact 10 (.full [5,3,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [5,3,2] (Equiv.refl (Fin 10)) sgB949 sgT949) sgFlag949 ≠ 0
  rw [sgCert949]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6682_oai : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg1033 sg949

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6682_oai := @OAI.UniversalTensorSquare.sg6682_oai
