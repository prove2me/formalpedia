-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_20All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:21:06.826493+00:00
-- url     : https://prove2.me/submissions/ada43caf-94ca-4409-86e4-ef08905cf9fe

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US011
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_19All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg1023
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1329
import Theorems.Thm_OAI_UniversalTensorSquare_sg166
import Theorems.Thm_OAI_UniversalTensorSquare_sg16690
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg17188
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg194
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg20521
import Theorems.Thm_OAI_UniversalTensorSquare_sg20633
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg265
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg2707
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg32227
import Theorems.Thm_OAI_UniversalTensorSquare_sg32228
import Theorems.Thm_OAI_UniversalTensorSquare_sg32229
import Theorems.Thm_OAI_UniversalTensorSquare_sg32231
import Theorems.Thm_OAI_UniversalTensorSquare_sg32233
import Theorems.Thm_OAI_UniversalTensorSquare_sg32235
import Theorems.Thm_OAI_UniversalTensorSquare_sg32237
import Theorems.Thm_OAI_UniversalTensorSquare_sg32238
import Theorems.Thm_OAI_UniversalTensorSquare_sg32239
import Theorems.Thm_OAI_UniversalTensorSquare_sg32240
import Theorems.Thm_OAI_UniversalTensorSquare_sg32242
import Theorems.Thm_OAI_UniversalTensorSquare_sg32243
import Theorems.Thm_OAI_UniversalTensorSquare_sg32244
import Theorems.Thm_OAI_UniversalTensorSquare_sg3523
import Theorems.Thm_OAI_UniversalTensorSquare_sg3964
import Theorems.Thm_OAI_UniversalTensorSquare_sg4834
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg792
import Theorems.Thm_OAI_UniversalTensorSquare_sgCert194

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

lemma sg762 : RowSquare [3,3,1,1,1,1] [2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg32

lemma sg1061 : RowSquare [6,2,2] [2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg32

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

lemma sg1758 : RowSquare [6,2,1,1,1,1] [2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg265

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 4. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2114 : RowSquare [5,1,1,1,1,1,1,1,1] [8,5] := by
  exact rowSquare_join (by decide) sg7 sg1023

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2528 : RowSquare [4,3,2,1,1,1,1,1] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg194

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3732 : RowSquare [9,3,3] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg1061

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 10. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4841 : RowSquare [6,3,2,1,1,1,1,1,1] [3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1758

lemma sg4844 : RowSquare [6,3,2,2,2,2] [4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg166 sg762

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4933 : RowSquare [9,1,1,1,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg2114

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3353 : RowSquare [6,4,2,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg762

lemma sg3359 : RowSquare [6,4,3,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg792

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 9. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4434 : RowSquare [9,2,2,1,1,1] [2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1327

lemma sg4435 : RowSquare [9,2,2,1,1,1] [3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1329

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15665 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2251 sg4834

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16217 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3359 sg4434

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20520 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4841

lemma sg20522 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2707 sg4834

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20741 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2528 sg4933

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 51. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20953 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,6] := by
  exact rowSquare_join (by decide) sg3732 sg4844

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17186 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3353 sg4435

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 79. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg32226 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg15665 sg20953

lemma sg32230 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20520 sg17186

lemma sg32232 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20741 sg16217

lemma sg32234 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20521 sg17186

lemma sg32236 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17186

lemma sg32241 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16690

lemma sg32245 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20520 sg17188

lemma sg32246 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20521 sg17188

lemma sg32247 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17188

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree62_18All : degreeTree62_18.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32236,⟨sg32231,⟨sg32228,⟨sg32227,⟨sg32226,True.intro,True.intro⟩,True.intro⟩,⟨sg32230,⟨sg32229,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32234,⟨sg32233,⟨sg32232,True.intro,True.intro⟩,True.intro⟩,⟨sg32235,True.intro,True.intro⟩⟩⟩,⟨sg32242,⟨sg32239,⟨sg32238,⟨sg32237,True.intro,True.intro⟩,True.intro⟩,⟨sg32241,⟨sg32240,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32245,⟨sg32244,⟨sg32243,True.intro,True.intro⟩,True.intro⟩,⟨sg32246,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_20All_oai : degreeTree62_20.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32247,degreeTree62_18All,degreeTree62_19All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_20All_oai := @OAI.UniversalTensorSquare.degreeTree62_20All_oai
