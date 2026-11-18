-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_194All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:40:29.568144+00:00
-- url     : https://prove2.me/submissions/4cc6ccfd-3998-44ac-be99-a54d2d9c758e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg10280
import Theorems.Thm_OAI_UniversalTensorSquare_sg10676
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg26146
import Theorems.Thm_OAI_UniversalTensorSquare_sg26151
import Theorems.Thm_OAI_UniversalTensorSquare_sg26152
import Theorems.Thm_OAI_UniversalTensorSquare_sg26153
import Theorems.Thm_OAI_UniversalTensorSquare_sg26154
import Theorems.Thm_OAI_UniversalTensorSquare_sg26156
import Theorems.Thm_OAI_UniversalTensorSquare_sg26158
import Theorems.Thm_OAI_UniversalTensorSquare_sg26159
import Theorems.Thm_OAI_UniversalTensorSquare_sg6915
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg8350
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425
import Theorems.Thm_OAI_UniversalTensorSquare_sg8427
import Theorems.Thm_OAI_UniversalTensorSquare_sg8429
import Theorems.Thm_OAI_UniversalTensorSquare_sg8430
import Theorems.Thm_OAI_UniversalTensorSquare_sg8730
import Theorems.Thm_OAI_UniversalTensorSquare_sg9493
import Theorems.Thm_OAI_UniversalTensorSquare_sg9551

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6919 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1001 sg1001

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10278 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6915

lemma sg10284 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg6919

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg808 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26147 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9551

lemma sg26148 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10280

lemma sg26149 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10676

lemma sg26150 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10278

lemma sg26155 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10284

lemma sg26157 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8730 sg9493

lemma sg26160 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10280

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree43_194All_oai : degreeTree43_194.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26153,⟨sg26149,⟨sg26147,⟨sg26146,True.intro,True.intro⟩,⟨sg26148,True.intro,True.intro⟩⟩,⟨sg26151,⟨sg26150,True.intro,True.intro⟩,⟨sg26152,True.intro,True.intro⟩⟩⟩,⟨sg26157,⟨sg26155,⟨sg26154,True.intro,True.intro⟩,⟨sg26156,True.intro,True.intro⟩⟩,⟨sg26159,⟨sg26158,True.intro,True.intro⟩,⟨sg26160,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_194All_oai := @OAI.UniversalTensorSquare.degreeTree43_194All_oai
