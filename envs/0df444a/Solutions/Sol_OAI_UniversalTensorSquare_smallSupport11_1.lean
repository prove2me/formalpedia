-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:59:23.608695+00:00
-- url     : https://prove2.me/submissions/0e352c5f-f745-41fa-a7ce-afbdd74ca8e4

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

lemma smallCert11_1 : solveChoices smallChoices11_1 (.full [5,2,2,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [5,2,2,1,1] (Equiv.refl (Fin 11)) smallB11_1 smallT11_1) smallFlag11_1 = -10 := by
  decide +kernel

lemma smallSupport11_1_oai : RowSquare [4,3,3,1] [5,3,1,1,1] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [5,2,2,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_1 smallT11_1 smallFlag11_1 smallChoices11_1
  change solveChoices smallChoices11_1 (.full [5,2,2,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [5,2,2,1,1] (Equiv.refl (Fin 11)) smallB11_1 smallT11_1) smallFlag11_1 ≠ 0
  rw [smallCert11_1]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_1_oai := @OAI.UniversalTensorSquare.smallSupport11_1_oai
