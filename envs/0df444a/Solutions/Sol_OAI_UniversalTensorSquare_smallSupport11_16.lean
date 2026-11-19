-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_16
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:01:59.772935+00:00
-- url     : https://prove2.me/submissions/15bc3bf7-2ce1-4723-bf50-7c4229c96610

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

lemma smallCert11_16 : solveChoices smallChoices11_16 (.full [3,3,2,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,3,2,1,1,1] (Equiv.refl (Fin 11)) smallB11_16 smallT11_16) smallFlag11_16 = -1 := by
  decide +kernel

lemma smallSupport11_16_oai : RowSquare [4,3,3,1] [6,3,2] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [3,3,2,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_16 smallT11_16 smallFlag11_16 smallChoices11_16
  change solveChoices smallChoices11_16 (.full [3,3,2,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,3,2,1,1,1] (Equiv.refl (Fin 11)) smallB11_16 smallT11_16) smallFlag11_16 ≠ 0
  rw [smallCert11_16]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_16_oai := @OAI.UniversalTensorSquare.smallSupport11_16_oai
