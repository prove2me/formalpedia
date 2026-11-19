-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport13_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:10:18.012887+00:00
-- url     : https://prove2.me/submissions/724b6d64-7360-4e6d-b670-b683b7c8cbec

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US015
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_choices
import Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_2

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_ChoiceCertificates13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choice certificates in degree thirteen. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupport13_2_oai : RowSquare [4,4,3,2] [7,2,1,1,1,1] := by
  apply rowSquare_choices (n := 13) (cs := [4,4,3,2]) (ts := [6,2,1,1,1,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB13_2 smallT13_2 smallFlag13_2 smallChoices13_2
  change solveChoices smallChoices13_2 (.full [6,2,1,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [6,2,1,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_2 smallT13_2) smallFlag13_2 ≠ 0
  rw [smallCert13_2]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport13_2_oai := @OAI.UniversalTensorSquare.smallSupport13_2_oai
