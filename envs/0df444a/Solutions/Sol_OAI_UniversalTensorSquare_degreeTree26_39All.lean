-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree26_39All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T22:14:15.003454+00:00
-- url     : https://prove2.me/submissions/6ef3efb6-0263-4f11-b129-d56cea651876
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg13319
import Theorems.Thm_OAI_UniversalTensorSquare_sg13322
import Theorems.Thm_OAI_UniversalTensorSquare_sg13323
import Theorems.Thm_OAI_UniversalTensorSquare_sg13324
import Theorems.Thm_OAI_UniversalTensorSquare_sg13326
import Theorems.Thm_OAI_UniversalTensorSquare_sg13327
import Theorems.Thm_OAI_UniversalTensorSquare_sg13329
import Theorems.Thm_OAI_UniversalTensorSquare_sg13330
import Theorems.Thm_OAI_UniversalTensorSquare_sg13331
import Theorems.Thm_OAI_UniversalTensorSquare_sg13333
import Theorems.Thm_OAI_UniversalTensorSquare_sg1650
import Theorems.Thm_OAI_UniversalTensorSquare_sg61

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

lemma sg59 : RowSquare [2,2,1,1] [4,2] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg60 : RowSquare [2,2,1,1] [5,1] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg207 : RowSquare [4,3] [2,2,2,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg208 : RowSquare [4,3] [3,2,1,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg209 : RowSquare [4,3] [3,2,2] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg210 : RowSquare [4,3] [3,3,1] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg213 : RowSquare [4,3] [4,3] := by
  exact rowSquare_short 3 1 (by decide) (by decide) (by decide)
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

lemma sg1651 : RowSquare [4,4,2,2] [2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg60 sg61

lemma sg1652 : RowSquare [4,4,2,2] [2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg59 sg61

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

lemma sg5934 : RowSquare [4,4,2,2,2,2,2,1] [5,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg213 sg1650

lemma sg5935 : RowSquare [4,4,2,2,2,2,2,1] [5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg1651

lemma sg5936 : RowSquare [4,4,2,2,2,2,2,1] [5,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg1652

lemma sg5937 : RowSquare [4,4,2,2,2,2,2,1] [5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg1652

lemma sg5945 : RowSquare [4,4,2,2,2,2,2,1] [6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg213 sg1651

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13320 : RowSquare [8,7,2,2,2,2,2,1] [8,6,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg5934

lemma sg13321 : RowSquare [8,7,2,2,2,2,2,1] [8,6,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg5945

lemma sg13325 : RowSquare [8,7,2,2,2,2,2,1] [8,6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg5936

lemma sg13328 : RowSquare [8,7,2,2,2,2,2,1] [8,6,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg5935

lemma sg13332 : RowSquare [8,7,2,2,2,2,2,1] [8,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg5937

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree26_39All_oai : degreeTree26_39.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13326,⟨sg13322,⟨sg13320,⟨sg13319,True.intro,True.intro⟩,⟨sg13321,True.intro,True.intro⟩⟩,⟨sg13324,⟨sg13323,True.intro,True.intro⟩,⟨sg13325,True.intro,True.intro⟩⟩⟩,⟨sg13330,⟨sg13328,⟨sg13327,True.intro,True.intro⟩,⟨sg13329,True.intro,True.intro⟩⟩,⟨sg13332,⟨sg13331,True.intro,True.intro⟩,⟨sg13333,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree26_39All_oai := @OAI.UniversalTensorSquare.degreeTree26_39All_oai
