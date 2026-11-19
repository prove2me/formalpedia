-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:05:47.075703+00:00
-- url     : https://prove2.me/submissions/e1002066-02a8-4fcd-97f9-c77ad6e677c2

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US013
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 0. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert11_3 : solveChoices smallChoices11_3 (.full [5,1,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [5,1,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_3 smallT11_3) smallFlag11_3 = -2 := by
  decide +kernel

lemma smallSupport11_3_oai : RowSquare [4,3,3,1] [7,1,1,1,1] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [5,1,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_3 smallT11_3 smallFlag11_3 smallChoices11_3
  change solveChoices smallChoices11_3 (.full [5,1,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [5,1,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_3 smallT11_3) smallFlag11_3 ≠ 0
  rw [smallCert11_3]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_3_oai := @OAI.UniversalTensorSquare.smallSupport11_3_oai
