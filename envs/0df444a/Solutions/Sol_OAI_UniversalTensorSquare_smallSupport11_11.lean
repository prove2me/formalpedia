-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:59:34.859612+00:00
-- url     : https://prove2.me/submissions/2be20553-123b-4dba-91e3-2c3f5de58357

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US013
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert11_11 : solveChoices smallChoices11_11 (.full [4,2,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [4,2,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_11 smallT11_11) smallFlag11_11 = 3 := by
  decide +kernel

lemma smallSupport11_11_oai : RowSquare [4,3,3,1] [7,2,1,1] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [4,2,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_11 smallT11_11 smallFlag11_11 smallChoices11_11
  change solveChoices smallChoices11_11 (.full [4,2,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [4,2,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_11 smallT11_11) smallFlag11_11 ≠ 0
  rw [smallCert11_11]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_11_oai := @OAI.UniversalTensorSquare.smallSupport11_11_oai
