-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:06:44.909409+00:00
-- url     : https://prove2.me/submissions/314d1f80-d0de-4f3c-a186-aa013c475e68

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US014
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_11 : solveChoices smallChoices13_11 (.full [5,2,2,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,2,2,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_11 smallT13_11) smallFlag13_11 = 1 := by
  decide +kernel

lemma smallSupport13_11_oai : RowSquare [4,4,3,2] [7,3,1,1,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [5,2,2,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_11 smallT13_11 smallFlag13_11 smallChoices13_11
  change solveChoices smallChoices13_11 (.full [5,2,2,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,2,2,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_11 smallT13_11) smallFlag13_11 ≠ 0
  rw [smallCert13_11]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_11_oai := @OAI.UniversalTensorSquare.smallSupport13_11_oai
