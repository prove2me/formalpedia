-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg23566
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T18:19:45.69052+00:00
-- url     : https://prove2.me/submissions/af13f2f1-3991-4473-9bb0-9f9370b33d42

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg18279

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

lemma sgCert887 : solveCompact 10 (.full [4,2,2,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [4,2,2,2] (Equiv.refl (Fin 10)) sgB887 sgT887) sgFlag887 = 1 := by
  decide +kernel

lemma sg887 : RowSquare [4,4,1,1] [4,4,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [4,2,2,2]) (ts := [4,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB887 sgT887 sgFlag887
  change solveCompact 10 (.full [4,2,2,2]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [4,2,2,2] (Equiv.refl (Fin 10)) sgB887 sgT887) sgFlag887 ≠ 0
  rw [sgCert887]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23566_oai : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg887 sg18279

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg23566_oai := @OAI.UniversalTensorSquare.sg23566_oai
