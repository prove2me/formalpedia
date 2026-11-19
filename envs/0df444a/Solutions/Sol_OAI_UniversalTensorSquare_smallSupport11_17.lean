-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_17
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:02:05.445481+00:00
-- url     : https://prove2.me/submissions/ce26433c-b563-49d3-935d-1355b6e85fff

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US013
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert11_17 : solveChoices smallChoices11_17 (.full [3,3,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,3,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_17 smallT11_17) smallFlag11_17 = 18 := by
  decide +kernel

lemma smallSupport11_17_oai : RowSquare [4,3,3,1] [7,2,2] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [3,3,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_17 smallT11_17 smallFlag11_17 smallChoices11_17
  change solveChoices smallChoices11_17 (.full [3,3,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,3,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_17 smallT11_17) smallFlag11_17 ≠ 0
  rw [smallCert11_17]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_17_oai := @OAI.UniversalTensorSquare.smallSupport11_17_oai
