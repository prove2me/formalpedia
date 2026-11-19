-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:05:52.731639+00:00
-- url     : https://prove2.me/submissions/1168d72a-739f-4326-9452-df4bb116dfbf

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

lemma smallCert11_4 : solveChoices smallChoices11_4 (.full [4,4,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [4,4,1,1,1] (Equiv.refl (Fin 11)) smallB11_4 smallT11_4) smallFlag11_4 = -4 := by
  decide +kernel

lemma smallSupport11_4_oai : RowSquare [4,3,3,1] [5,2,2,2] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [4,4,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_4 smallT11_4 smallFlag11_4 smallChoices11_4
  change solveChoices smallChoices11_4 (.full [4,4,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [4,4,1,1,1] (Equiv.refl (Fin 11)) smallB11_4 smallT11_4) smallFlag11_4 ≠ 0
  rw [smallCert11_4]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_4_oai := @OAI.UniversalTensorSquare.smallSupport11_4_oai
