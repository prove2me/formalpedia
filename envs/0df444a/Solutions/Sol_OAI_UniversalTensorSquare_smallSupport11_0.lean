-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:59:18.115041+00:00
-- url     : https://prove2.me/submissions/f9c1794c-4513-46db-bb08-7771510097e6

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

lemma smallCert11_0 : solveChoices smallChoices11_0 (.full [6,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [6,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_0 smallT11_0) smallFlag11_0 = 1 := by
  decide +kernel

lemma smallSupport11_0_oai : RowSquare [4,3,3,1] [6,1,1,1,1,1] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [6,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_0 smallT11_0 smallFlag11_0 smallChoices11_0
  change solveChoices smallChoices11_0 (.full [6,1,1,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [6,1,1,1,1,1] (Equiv.refl (Fin 11)) smallB11_0 smallT11_0) smallFlag11_0 ≠ 0
  rw [smallCert11_0]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_0_oai := @OAI.UniversalTensorSquare.smallSupport11_0_oai
