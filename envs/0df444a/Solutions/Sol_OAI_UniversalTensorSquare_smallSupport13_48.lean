-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_48
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:26:25.018516+00:00
-- url     : https://prove2.me/submissions/0fd160f5-1cc6-41fd-8670-40a91a8a9dd2

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US019
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_48

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_48_oai : RowSquare [4,4,3,2] [8,5] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [2,2,2,2,2,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_48 smallT13_48 smallFlag13_48 smallChoices13_48
  change solveChoices smallChoices13_48 (.full [2,2,2,2,2,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [2,2,2,2,2,1,1,1] (Equiv.refl (Fin 13)) smallB13_48 smallT13_48) smallFlag13_48 ≠ 0
  rw [smallCert13_48]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_48_oai := @OAI.UniversalTensorSquare.smallSupport13_48_oai
