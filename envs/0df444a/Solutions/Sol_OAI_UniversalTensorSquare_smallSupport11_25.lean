-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_25
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:05:30.03158+00:00
-- url     : https://prove2.me/submissions/7ba3a0f8-673b-4a63-8572-72ea33f5a3cf

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US013
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert11_25 : solveChoices smallChoices11_25 (.full [2,2,2,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [2,2,2,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_25 smallT11_25) smallFlag11_25 = -8 := by
  decide +kernel

lemma smallSupport11_25_oai : RowSquare [4,3,3,1] [8,3] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [2,2,2,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_25 smallT11_25 smallFlag11_25 smallChoices11_25
  change solveChoices smallChoices11_25 (.full [2,2,2,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [2,2,2,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_25 smallT11_25) smallFlag11_25 ≠ 0
  rw [smallCert11_25]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_25_oai := @OAI.UniversalTensorSquare.smallSupport11_25_oai
