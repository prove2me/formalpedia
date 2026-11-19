-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupport11_14
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T23:59:51.770982+00:00
-- url     : https://prove2.me/submissions/72e54e1e-289e-4956-b1c3-907a6bf295fe

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCert11_14 : solveCompact 11 (.full [3,3,3,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,3,3,1,1] (Equiv.refl (Fin 11)) smallB11_14 smallT11_14) smallFlag11_14 = 7 := by
  decide +kernel

lemma smallSupport11_14_oai : RowSquare [4,3,3,1] [5,3,3] := by
  apply rowSquare_compact (n := 11) (cs := [4,3,3,1]) (ts := [3,3,3,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl smallB11_14 smallT11_14 smallFlag11_14
  change solveCompact 11 (.full [3,3,3,1,1]) (.full [4,3,3,1]) (.full [4,3,3,1])
    (certificateEdges [4,3,3,1] [4,3,3,1] [3,3,3,1,1] (Equiv.refl (Fin 11)) smallB11_14 smallT11_14) smallFlag11_14 ≠ 0
  rw [smallCert11_14]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupport11_14_oai := @OAI.UniversalTensorSquare.smallSupport11_14_oai
