-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg1015
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:30:28.519202+00:00
-- url     : https://prove2.me/submissions/5262e4c0-3ec6-441e-af6a-eb140bac85c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert1015

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1015_oai : RowSquare [6,1,1,1,1] [4,4,1,1] := by
  apply rowSquare_compact (n := 10) (cs := [5,1,1,1,1,1]) (ts := [4,2,2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB1015 sgT1015 sgFlag1015
  change solveCompact 10 (.full [4,2,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [4,2,2,2] (Equiv.refl (Fin 10)) sgB1015 sgT1015) sgFlag1015 ≠ 0
  rw [sgCert1015]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg1015_oai := @OAI.UniversalTensorSquare.sg1015_oai
