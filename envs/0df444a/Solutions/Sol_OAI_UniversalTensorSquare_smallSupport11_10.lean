-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:59:29.143851+00:00
-- url     : https://prove2.me/submissions/8f8e5e31-68ad-463c-9f52-786f2f9819dd

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

lemma smallCert11_10 : solveChoices smallChoices11_10 (.full [4,2,2,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [4,2,2,1,1,1] (Equiv.refl (Fin 11)) smallB11_10 smallT11_10) smallFlag11_10 = 5 := by
  decide +kernel

lemma smallSupport11_10_oai : RowSquare [4,3,3,1] [6,3,1,1] := by
  apply rowSquare_choices (n := 11) (cs := [4,3,3,1]) (ts := [4,2,2,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_10 smallT11_10 smallFlag11_10 smallChoices11_10
  change solveChoices smallChoices11_10 (.full [4,2,2,1,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [4,2,2,1,1,1] (Equiv.refl (Fin 11)) smallB11_10 smallT11_10) smallFlag11_10 ≠ 0
  rw [smallCert11_10]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_10_oai := @OAI.UniversalTensorSquare.smallSupport11_10_oai
