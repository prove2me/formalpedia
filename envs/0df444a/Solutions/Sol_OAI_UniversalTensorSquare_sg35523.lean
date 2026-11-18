-- Prove2me | solution 1 for OAI.UniversalTensorSquare.sg35523
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T05:03:33.53133+00:00
-- url     : https://prove2.me/submissions/2598956f-3f68-4079-898b-f0e91e97aca2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_Saxl_orbitAverage_base
import Theorems.Thm_OAI_Saxl_specht_sign_transpose_uts
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_of_cols
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg10
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20316
import Theorems.Thm_OAI_UniversalTensorSquare_sg3633
import Theorems.Thm_OAI_UniversalTensorSquare_sg396
import Theorems.Thm_OAI_UniversalTensorSquare_sg516
import Theorems.Thm_OAI_UniversalTensorSquare_sg92
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert10
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert17
import Theorems.Thm_OAI_UniversalTensorSquare_transposeRows_eq

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLocalLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Local Leaves. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg41 : RowSquare [3,2] [3,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1300 : RowSquare [5,3,3] [3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg516

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12837 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1] [6,3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1300 sg3633

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 44. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18350 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg41 sg12837

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 87. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg35523_oai : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,7,7,6,6,6,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18350

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.sg35523_oai := @OAI.UniversalTensorSquare.sg35523_oai
