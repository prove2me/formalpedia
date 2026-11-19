-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_45
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:26:07.180824+00:00
-- url     : https://prove2.me/submissions/2b8c34ba-6c88-4ff0-af99-4f4d503df3e8

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US019
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_45

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

lemma smallSupport13_45_oai : RowSquare [4,4,3,2] [5,5,3] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [3,3,3,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_45 smallT13_45 smallFlag13_45 smallChoices13_45
  change solveChoices smallChoices13_45 (.full [3,3,3,2,2]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,3,2,2] (Equiv.refl (Fin 13)) smallB13_45 smallT13_45) smallFlag13_45 ≠ 0
  rw [smallCert13_45]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_45_oai := @OAI.UniversalTensorSquare.smallSupport13_45_oai
