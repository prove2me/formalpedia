-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_32
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:24:47.079617+00:00
-- url     : https://prove2.me/submissions/e1246d3c-cfe1-473a-a91e-efb40f38a86a

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US017
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert13_32 : solveChoices smallChoices13_32 (.full [3,3,2,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,2,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_32 smallT13_32) smallFlag13_32 = 8 := by
  decide +kernel

lemma smallSupport13_32_oai : RowSquare [4,4,3,2] [8,3,2] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [3,3,2,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_32 smallT13_32 smallFlag13_32 smallChoices13_32
  change solveChoices smallChoices13_32 (.full [3,3,2,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,2,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_32 smallT13_32) smallFlag13_32 ≠ 0
  rw [smallCert13_32]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_32_oai := @OAI.UniversalTensorSquare.smallSupport13_32_oai
