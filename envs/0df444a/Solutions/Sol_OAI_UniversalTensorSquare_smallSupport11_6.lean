-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:06:03.931477+00:00
-- url     : https://prove2.me/submissions/13a7309d-7350-4b51-9334-8ddc4b297c8b

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

lemma smallCert11_6 : solveChoices smallChoices11_6 (.full [4,3,2,2]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [4,3,2,2] (Equiv.refl (Fin 11)) smallB11_6 smallT11_6) smallFlag11_6 = 5 := by
  decide +kernel

lemma smallSupport11_6_oai : RowSquare [4,3,3,1] [4,4,2,1] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [4,3,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_6 smallT11_6 smallFlag11_6 smallChoices11_6
  change solveChoices smallChoices11_6 (.full [4,3,2,2]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [4,3,2,2] (Equiv.refl (Fin 11)) smallB11_6 smallT11_6) smallFlag11_6 ≠ 0
  rw [smallCert11_6]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_6_oai := @OAI.UniversalTensorSquare.smallSupport11_6_oai
