-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_198All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:42:56.3425+00:00
-- url     : https://prove2.me/submissions/af5c31b2-84b4-428d-a978-038ddc3fb255
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10283
import Theorems.Thm_OAI_UniversalTensorSquare_sg10387
import Theorems.Thm_OAI_UniversalTensorSquare_sg10388
import Theorems.Thm_OAI_UniversalTensorSquare_sg10389
import Theorems.Thm_OAI_UniversalTensorSquare_sg10680
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg26194
import Theorems.Thm_OAI_UniversalTensorSquare_sg26195
import Theorems.Thm_OAI_UniversalTensorSquare_sg26196
import Theorems.Thm_OAI_UniversalTensorSquare_sg26197
import Theorems.Thm_OAI_UniversalTensorSquare_sg26199
import Theorems.Thm_OAI_UniversalTensorSquare_sg26200
import Theorems.Thm_OAI_UniversalTensorSquare_sg26204
import Theorems.Thm_OAI_UniversalTensorSquare_sg26205
import Theorems.Thm_OAI_UniversalTensorSquare_sg26206
import Theorems.Thm_OAI_UniversalTensorSquare_sg26207
import Theorems.Thm_OAI_UniversalTensorSquare_sg26208
import Theorems.Thm_OAI_UniversalTensorSquare_sg26210
import Theorems.Thm_OAI_UniversalTensorSquare_sg26211
import Theorems.Thm_OAI_UniversalTensorSquare_sg26212
import Theorems.Thm_OAI_UniversalTensorSquare_sg26213
import Theorems.Thm_OAI_UniversalTensorSquare_sg26214
import Theorems.Thm_OAI_UniversalTensorSquare_sg26215
import Theorems.Thm_OAI_UniversalTensorSquare_sg26217
import Theorems.Thm_OAI_UniversalTensorSquare_sg26218
import Theorems.Thm_OAI_UniversalTensorSquare_sg26220
import Theorems.Thm_OAI_UniversalTensorSquare_sg26221
import Theorems.Thm_OAI_UniversalTensorSquare_sg26222
import Theorems.Thm_OAI_UniversalTensorSquare_sg26224
import Theorems.Thm_OAI_UniversalTensorSquare_sg324
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg809
import Theorems.Thm_OAI_UniversalTensorSquare_sg8350
import Theorems.Thm_OAI_UniversalTensorSquare_sg8415
import Theorems.Thm_OAI_UniversalTensorSquare_sg8427
import Theorems.Thm_OAI_UniversalTensorSquare_sg8429
import Theorems.Thm_OAI_UniversalTensorSquare_sg9554

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

lemma sg590 : RowSquare [5,1,1,1,1] [2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg324

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1005 : RowSquare [6,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg590

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
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8195 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1005 sg1417

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

lemma sg8722 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9552 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8195

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

lemma sg26198 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9552

lemma sg26201 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9554

lemma sg26202 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10283

lemma sg26203 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10680

lemma sg26209 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10283

lemma sg26216 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10387

lemma sg26219 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10388

lemma sg26223 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10389

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

lemma degreeTree43_198All_oai : degreeTree43_198.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26209,⟨sg26201,⟨sg26197,⟨sg26195,⟨sg26194,True.intro,True.intro⟩,⟨sg26196,True.intro,True.intro⟩⟩,⟨sg26199,⟨sg26198,True.intro,True.intro⟩,⟨sg26200,True.intro,True.intro⟩⟩⟩,⟨sg26205,⟨sg26203,⟨sg26202,True.intro,True.intro⟩,⟨sg26204,True.intro,True.intro⟩⟩,⟨sg26207,⟨sg26206,True.intro,True.intro⟩,⟨sg26208,True.intro,True.intro⟩⟩⟩⟩,⟨sg26217,⟨sg26213,⟨sg26211,⟨sg26210,True.intro,True.intro⟩,⟨sg26212,True.intro,True.intro⟩⟩,⟨sg26215,⟨sg26214,True.intro,True.intro⟩,⟨sg26216,True.intro,True.intro⟩⟩⟩,⟨sg26221,⟨sg26219,⟨sg26218,True.intro,True.intro⟩,⟨sg26220,True.intro,True.intro⟩⟩,⟨sg26223,⟨sg26222,True.intro,True.intro⟩,⟨sg26224,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_198All_oai := @OAI.UniversalTensorSquare.degreeTree43_198All_oai
