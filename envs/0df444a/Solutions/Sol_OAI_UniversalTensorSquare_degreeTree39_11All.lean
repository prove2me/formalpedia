-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_11All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:59:40.667367+00:00
-- url     : https://prove2.me/submissions/b65ca4d6-c330-4fcb-aacd-c777f54eaa5f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg21875
import Theorems.Thm_OAI_UniversalTensorSquare_sg21876
import Theorems.Thm_OAI_UniversalTensorSquare_sg21877
import Theorems.Thm_OAI_UniversalTensorSquare_sg21878
import Theorems.Thm_OAI_UniversalTensorSquare_sg21879
import Theorems.Thm_OAI_UniversalTensorSquare_sg21880
import Theorems.Thm_OAI_UniversalTensorSquare_sg21881
import Theorems.Thm_OAI_UniversalTensorSquare_sg21882
import Theorems.Thm_OAI_UniversalTensorSquare_sg21883
import Theorems.Thm_OAI_UniversalTensorSquare_sg21884
import Theorems.Thm_OAI_UniversalTensorSquare_sg21885
import Theorems.Thm_OAI_UniversalTensorSquare_sg21886
import Theorems.Thm_OAI_UniversalTensorSquare_sg21887
import Theorems.Thm_OAI_UniversalTensorSquare_sg21888
import Theorems.Thm_OAI_UniversalTensorSquare_sg21889
import Theorems.Thm_OAI_UniversalTensorSquare_sg21890
import Theorems.Thm_OAI_UniversalTensorSquare_sg21891
import Theorems.Thm_OAI_UniversalTensorSquare_sg21892
import Theorems.Thm_OAI_UniversalTensorSquare_sg21893
import Theorems.Thm_OAI_UniversalTensorSquare_sg21894
import Theorems.Thm_OAI_UniversalTensorSquare_sg21895
import Theorems.Thm_OAI_UniversalTensorSquare_sg21897
import Theorems.Thm_OAI_UniversalTensorSquare_sg21900
import Theorems.Thm_OAI_UniversalTensorSquare_sg21901
import Theorems.Thm_OAI_UniversalTensorSquare_sg21902
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg6309
import Theorems.Thm_OAI_UniversalTensorSquare_sg6310
import Theorems.Thm_OAI_UniversalTensorSquare_sg6410
import Theorems.Thm_OAI_UniversalTensorSquare_sg7

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 0. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg46 : RowSquare [4,1] [3,2] := by
  exact rowSquare_join (by decide) sg0 sg17

lemma sg111 : RowSquare [2,1,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

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

lemma sg1417 : RowSquare [6,3,1,1] [2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg178

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1757 : RowSquare [6,2,1,1,1,1] [2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg111

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 13. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5900 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg1417

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg6803 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5900

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7314 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg1757

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21896 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6309 sg7314

lemma sg21898 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6410 sg6803

lemma sg21899 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,4,2,2,2] := by
  exact rowSquare_join (by decide) sg6310 sg7314

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree39_11All_oai : degreeTree39_11.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21889,⟨sg21882,⟨sg21878,⟨sg21876,⟨sg21875,True.intro,True.intro⟩,⟨sg21877,True.intro,True.intro⟩⟩,⟨sg21880,⟨sg21879,True.intro,True.intro⟩,⟨sg21881,True.intro,True.intro⟩⟩⟩,⟨sg21886,⟨sg21884,⟨sg21883,True.intro,True.intro⟩,⟨sg21885,True.intro,True.intro⟩⟩,⟨sg21888,⟨sg21887,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21896,⟨sg21893,⟨sg21891,⟨sg21890,True.intro,True.intro⟩,⟨sg21892,True.intro,True.intro⟩⟩,⟨sg21895,⟨sg21894,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21900,⟨sg21898,⟨sg21897,True.intro,True.intro⟩,⟨sg21899,True.intro,True.intro⟩⟩,⟨sg21902,⟨sg21901,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_11All_oai := @OAI.UniversalTensorSquare.degreeTree39_11All_oai
