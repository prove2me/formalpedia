-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_19
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:02:17.458073+00:00
-- url     : https://prove2.me/submissions/842e30a4-6c8d-4ff0-9cd2-5a56cc5c81e9

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

lemma smallCert11_19 : solveChoices smallChoices11_19 (.full [3,2,2,2,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,2,2,2,1,1] (Equiv.refl (Fin 11)) smallB11_19 smallT11_19) smallFlag11_19 = -2 := by
  decide +kernel

lemma smallSupport11_19_oai : RowSquare [4,3,3,1] [6,4,1] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [3,2,2,2,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_19 smallT11_19 smallFlag11_19 smallChoices11_19
  change solveChoices smallChoices11_19 (.full [3,2,2,2,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,2,2,2,1,1] (Equiv.refl (Fin 11)) smallB11_19 smallT11_19) smallFlag11_19 ≠ 0
  rw [smallCert11_19]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_19_oai := @OAI.UniversalTensorSquare.smallSupport11_19_oai
