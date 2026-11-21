-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg21914
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T10:26:16.607659+00:00
-- url     : https://prove2.me/submissions/8a0afd6d-9124-43af-9570-8d98654a7b86

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg6772
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert814

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg814 : RowSquare [4,2,1,1,1,1] [3,3,1,1,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,1,1,1,1]) (ts := [6,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB814 sgT814 sgFlag814
  change solveCompact 10 (.full [6,2,2]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB814 sgT814) sgFlag814 ≠ 0
  rw [sgCert814]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6428 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg814

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21914_oai : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg6428 sg6772

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg21914_oai := @OAI.UniversalTensorSquare.sg21914_oai
