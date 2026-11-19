-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:26:01.227073+00:00
-- url     : https://prove2.me/submissions/f0c57f64-706e-43d0-aeb7-788159b3ea26

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US019
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_44

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_44_oai : RowSquare [4,4,3,2] [5,4,4] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [3,3,3,3,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_44 smallT13_44 smallFlag13_44 smallChoices13_44
  change solveChoices smallChoices13_44 (.full [3,3,3,3,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,3,3,1] (Equiv.refl (Fin 13)) smallB13_44 smallT13_44) smallFlag13_44 ≠ 0
  rw [smallCert13_44]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_44_oai := @OAI.UniversalTensorSquare.smallSupport13_44_oai
