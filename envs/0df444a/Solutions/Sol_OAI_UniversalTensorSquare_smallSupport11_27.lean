-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_27
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:05:41.438395+00:00
-- url     : https://prove2.me/submissions/823f325d-8ec1-4a80-8bc1-676e212ad6e3

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

lemma smallCert11_27 : solveChoices smallChoices11_27 (.full [2,1,1,1,1,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [2,1,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_27 smallT11_27) smallFlag11_27 = -24 := by
  decide +kernel

lemma smallSupport11_27_oai : RowSquare [4,3,3,1] [10,1] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [2,1,1,1,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_27 smallT11_27 smallFlag11_27 smallChoices11_27
  change solveChoices smallChoices11_27 (.full [2,1,1,1,1,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [2,1,1,1,1,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_27 smallT11_27) smallFlag11_27 ≠ 0
  rw [smallCert11_27]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_27_oai := @OAI.UniversalTensorSquare.smallSupport11_27_oai
