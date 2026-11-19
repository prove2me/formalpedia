-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_22
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:02:40.295927+00:00
-- url     : https://prove2.me/submissions/3f9ed06b-465a-4632-9a65-f9df846897a5

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US013
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert11_22 : solveChoices smallChoices11_22 (.full [3,1,1,1,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_22 smallT11_22) smallFlag11_22 = 8 := by
  decide +kernel

lemma smallSupport11_22_oai : RowSquare [4,3,3,1] [9,1,1] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [3,1,1,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_22 smallT11_22 smallFlag11_22 smallChoices11_22
  change solveChoices smallChoices11_22 (.full [3,1,1,1,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_22 smallT11_22) smallFlag11_22 ≠ 0
  rw [smallCert11_22]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_22_oai := @OAI.UniversalTensorSquare.smallSupport11_22_oai
