-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg6872
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T21:13:31.719681+00:00
-- url     : https://prove2.me/submissions/4fc87400-8a16-400c-be7d-48c189e5f4a1

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg838
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003

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

lemma sgCert884 : solveCompact 10 (.full [6,2,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [6,2,2] (Equiv.refl (Fin 10)) sgB884 sgT884) sgFlag884 = 6 := by
  decide +kernel

lemma sg884 : RowSquare [4,4,1,1] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB884 sgT884 sgFlag884
  change solveCompact 10 (.full [6,2,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [6,2,2] (Equiv.refl (Fin 10)) sgB884 sgT884) sgFlag884 ≠ 0
  rw [sgCert884]
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

lemma sg6872_oai : RowSquare [5,4,2,2,2,2,2,1] [5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg838 sg884

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg6872_oai := @OAI.UniversalTensorSquare.sg6872_oai
