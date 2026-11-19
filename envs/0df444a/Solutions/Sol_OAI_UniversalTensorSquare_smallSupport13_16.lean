-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_16
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:09:54.665964+00:00
-- url     : https://prove2.me/submissions/5124ab98-cd74-4e1e-8496-a4d6617278ee

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US014
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_16

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_16_oai : RowSquare [4,4,3,2] [6,3,2,2] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [4,4,2,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_16 smallT13_16 smallFlag13_16 smallChoices13_16
  change solveChoices smallChoices13_16 (.full [4,4,2,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,4,2,1,1,1] (Equiv.refl (Fin 13)) smallB13_16 smallT13_16) smallFlag13_16 ≠ 0
  rw [smallCert13_16]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_16_oai := @OAI.UniversalTensorSquare.smallSupport13_16_oai
