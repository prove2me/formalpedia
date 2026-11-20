-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_24
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:10:46.418135+00:00
-- url     : https://prove2.me/submissions/38925200-a548-4154-9f4f-fd1f82b83015

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US016
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_24

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_24_oai : RowSquare [4,4,3,2] [6,5,1,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [4,2,2,2,2,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_24 smallT13_24 smallFlag13_24 smallChoices13_24
  change solveChoices smallChoices13_24 (.full [4,2,2,2,2,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,2,2,2,2,1] (Equiv.refl (Fin 13)) smallB13_24 smallT13_24) smallFlag13_24 ≠ 0
  rw [smallCert13_24]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_24_oai := @OAI.UniversalTensorSquare.smallSupport13_24_oai
