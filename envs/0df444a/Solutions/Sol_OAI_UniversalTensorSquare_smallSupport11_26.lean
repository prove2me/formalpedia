-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_26
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:05:35.712879+00:00
-- url     : https://prove2.me/submissions/4a5a861b-6e3a-47fa-acee-ba2c3d960aad

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

lemma smallCert11_26 : solveChoices smallChoices11_26 (.full [2,2,1,1,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [2,2,1,1,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_26 smallT11_26) smallFlag11_26 = -4 := by
  decide +kernel

lemma smallSupport11_26_oai : RowSquare [4,3,3,1] [9,2] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [2,2,1,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_26 smallT11_26 smallFlag11_26 smallChoices11_26
  change solveChoices smallChoices11_26 (.full [2,2,1,1,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [2,2,1,1,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_26 smallT11_26) smallFlag11_26 ≠ 0
  rw [smallCert11_26]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_26_oai := @OAI.UniversalTensorSquare.smallSupport11_26_oai
