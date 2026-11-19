-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:25:32.603133+00:00
-- url     : https://prove2.me/submissions/8fdd6258-819e-4fdb-b3ae-5c0ab61f028b

import Mathlib
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_4

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_4_oai : RowSquare [4,4,3,2] [6,2,2,2,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [5,4,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_4 smallT13_4 smallFlag13_4
  change solveCompact 13 (.full [5,4,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,4,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_4 smallT13_4) smallFlag13_4 ≠ 0
  rw [smallCert13_4]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_4_oai := @OAI.UniversalTensorSquare.smallSupport13_4_oai
