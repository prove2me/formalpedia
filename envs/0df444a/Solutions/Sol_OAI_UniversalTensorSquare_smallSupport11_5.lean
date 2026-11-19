-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:05:58.321295+00:00
-- url     : https://prove2.me/submissions/333cd91f-3352-4803-8b0f-80649dabbb8c

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US013
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert11_5 : solveChoices smallChoices11_5 (.full [4,3,3,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [4,3,3,1] (Equiv.refl (Fin 11)) smallB11_5 smallT11_5) smallFlag11_5 = 5 := by
  decide +kernel

lemma smallSupport11_5_oai : RowSquare [4,3,3,1] [4,3,3,1] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [4,3,3,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_5 smallT11_5 smallFlag11_5 smallChoices11_5
  change solveChoices smallChoices11_5 (.full [4,3,3,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [4,3,3,1] (Equiv.refl (Fin 11)) smallB11_5 smallT11_5) smallFlag11_5 ≠ 0
  rw [smallCert11_5]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_5_oai := @OAI.UniversalTensorSquare.smallSupport11_5_oai
