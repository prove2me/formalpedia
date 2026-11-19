-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:26:48.715512+00:00
-- url     : https://prove2.me/submissions/6fd08881-4ecc-4f5c-8fb9-e6d3edb94709
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US005
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_6

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

lemma smallSupport13_6_oai : RowSquare [4,4,3,2] [5,4,2,1,1] := by
  apply rowSquare_compact (n := 13) (cs := [4,4,3,2]) (ts := [5,3,2,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_6 smallT13_6 smallFlag13_6
  change solveCompact 13 (.full [5,3,2,2,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,3,2,2,1] (Equiv.refl (Fin 13)) smallB13_6 smallT13_6) smallFlag13_6 ≠ 0
  rw [smallCert13_6]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_6_oai := @OAI.UniversalTensorSquare.smallSupport13_6_oai
