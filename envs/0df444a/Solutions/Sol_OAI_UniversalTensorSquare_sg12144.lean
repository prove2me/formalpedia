-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg12144
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T21:05:28.584209+00:00
-- url     : https://prove2.me/submissions/bd88abda-12a2-410b-a350-8338e3712144
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg2583

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert767 : solveCompact 10 (.full [4,4,2]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB767 sgT767) sgFlag767 = 10 := by
  decide +kernel

lemma sg767 : RowSquare [3,3,1,1,1,1] [3,3,2,2] := by
  apply rowSquare_compact (n := 10) (cs := [3,3,1,1,1,1]) (ts := [4,4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB767 sgT767 sgFlag767
  change solveCompact 10 (.full [4,4,2]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [4,4,2] (Equiv.refl (Fin 10)) sgB767 sgT767) sgFlag767 ≠ 0
  rw [sgCert767]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12144_oai : RowSquare [8,6,2,2,2,2,1,1] [7,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg767 sg2583

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg12144_oai := @OAI.UniversalTensorSquare.sg12144_oai
