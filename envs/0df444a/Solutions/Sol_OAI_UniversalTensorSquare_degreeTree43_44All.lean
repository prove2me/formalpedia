-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_44All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:48:41.141727+00:00
-- url     : https://prove2.me/submissions/4614ff14-c2fa-4301-80ec-0700cbac484f

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10222
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1416
import Theorems.Thm_OAI_UniversalTensorSquare_sg1522
import Theorems.Thm_OAI_UniversalTensorSquare_sg24225
import Theorems.Thm_OAI_UniversalTensorSquare_sg24226
import Theorems.Thm_OAI_UniversalTensorSquare_sg24227
import Theorems.Thm_OAI_UniversalTensorSquare_sg24228
import Theorems.Thm_OAI_UniversalTensorSquare_sg24230
import Theorems.Thm_OAI_UniversalTensorSquare_sg24231
import Theorems.Thm_OAI_UniversalTensorSquare_sg24233
import Theorems.Thm_OAI_UniversalTensorSquare_sg24234
import Theorems.Thm_OAI_UniversalTensorSquare_sg24235
import Theorems.Thm_OAI_UniversalTensorSquare_sg24236
import Theorems.Thm_OAI_UniversalTensorSquare_sg24238
import Theorems.Thm_OAI_UniversalTensorSquare_sg24239
import Theorems.Thm_OAI_UniversalTensorSquare_sg24240
import Theorems.Thm_OAI_UniversalTensorSquare_sg24241
import Theorems.Thm_OAI_UniversalTensorSquare_sg24243
import Theorems.Thm_OAI_UniversalTensorSquare_sg24244
import Theorems.Thm_OAI_UniversalTensorSquare_sg24245
import Theorems.Thm_OAI_UniversalTensorSquare_sg24246
import Theorems.Thm_OAI_UniversalTensorSquare_sg24247
import Theorems.Thm_OAI_UniversalTensorSquare_sg24249
import Theorems.Thm_OAI_UniversalTensorSquare_sg24250
import Theorems.Thm_OAI_UniversalTensorSquare_sg24252
import Theorems.Thm_OAI_UniversalTensorSquare_sg24255
import Theorems.Thm_OAI_UniversalTensorSquare_sg265
import Theorems.Thm_OAI_UniversalTensorSquare_sg616
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg808
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg8730
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg9457
import Theorems.Thm_OAI_UniversalTensorSquare_sg9753
import Theorems.Thm_OAI_UniversalTensorSquare_sg9755
import Theorems.Thm_OAI_UniversalTensorSquare_sg9756

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

lemma sg813 : RowSquare [4,2,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg616

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

lemma sg1330 : RowSquare [6,1,1,1,1,1] [2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg265

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

lemma sg8183 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1522

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

lemma sg8733 : RowSquare [6,6,2,1,1,1,1,1,1,1] [4,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg813 sg1327

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

lemma sg9458 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1416 sg1330

lemma sg9482 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8183

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24229 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8730 sg9457

lemma sg24232 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9753

lemma sg24237 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8730 sg9458

lemma sg24242 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10222

lemma sg24248 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9755

lemma sg24251 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8721 sg9482

lemma sg24253 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9756

lemma sg24254 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8733 sg9458

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

lemma degreeTree43_44All_oai : degreeTree43_44.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24240,⟨sg24232,⟨sg24228,⟨sg24226,⟨sg24225,True.intro,True.intro⟩,⟨sg24227,True.intro,True.intro⟩⟩,⟨sg24230,⟨sg24229,True.intro,True.intro⟩,⟨sg24231,True.intro,True.intro⟩⟩⟩,⟨sg24236,⟨sg24234,⟨sg24233,True.intro,True.intro⟩,⟨sg24235,True.intro,True.intro⟩⟩,⟨sg24238,⟨sg24237,True.intro,True.intro⟩,⟨sg24239,True.intro,True.intro⟩⟩⟩⟩,⟨sg24248,⟨sg24244,⟨sg24242,⟨sg24241,True.intro,True.intro⟩,⟨sg24243,True.intro,True.intro⟩⟩,⟨sg24246,⟨sg24245,True.intro,True.intro⟩,⟨sg24247,True.intro,True.intro⟩⟩⟩,⟨sg24252,⟨sg24250,⟨sg24249,True.intro,True.intro⟩,⟨sg24251,True.intro,True.intro⟩⟩,⟨sg24254,⟨sg24253,True.intro,True.intro⟩,⟨sg24255,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_44All_oai := @OAI.UniversalTensorSquare.degreeTree43_44All_oai
