-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_29
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:24:24.290461+00:00
-- url     : https://prove2.me/submissions/478e5b9b-60bf-486b-af17-ff55d9ba53da

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US015
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_29

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_29_oai : RowSquare [4,4,3,2] [7,3,3] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [3,3,3,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_29 smallT13_29 smallFlag13_29 smallChoices13_29
  change solveChoices smallChoices13_29 (.full [3,3,3,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,3,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_29 smallT13_29) smallFlag13_29 ≠ 0
  rw [smallCert13_29]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_29_oai := @OAI.UniversalTensorSquare.smallSupport13_29_oai
