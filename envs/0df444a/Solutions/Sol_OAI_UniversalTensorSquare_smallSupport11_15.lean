-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_15
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:59:57.410195+00:00
-- url     : https://prove2.me/submissions/d78101a7-ccaf-4728-82bf-f9cdeebfa90d

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert11_15 : solveCompact 11 (.full [3,3,2,2,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,3,2,2,1] (Equiv.refl (Fin 11)) smallB11_15 smallT11_15) smallFlag11_15 = 2 := by
  decide +kernel

lemma smallSupport11_15_oai : RowSquare [4,3,3,1] [5,4,2] := by
  apply rowSquare_compact (n := 11) (cs := [4,3,3,1]) (ts := [3,3,2,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_15 smallT11_15 smallFlag11_15
  change solveCompact 11 (.full [3,3,2,2,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,3,2,2,1] (Equiv.refl (Fin 11)) smallB11_15 smallT11_15) smallFlag11_15 ≠ 0
  rw [smallCert11_15]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_15_oai := @OAI.UniversalTensorSquare.smallSupport11_15_oai
