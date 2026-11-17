-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_175All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:59:06.929947+00:00
-- url     : https://prove2.me/submissions/e4b38a6a-10e7-49d6-98c0-77f63ff7d7b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10230
import Theorems.Thm_OAI_UniversalTensorSquare_sg25888
import Theorems.Thm_OAI_UniversalTensorSquare_sg25889
import Theorems.Thm_OAI_UniversalTensorSquare_sg25891
import Theorems.Thm_OAI_UniversalTensorSquare_sg25892
import Theorems.Thm_OAI_UniversalTensorSquare_sg25893
import Theorems.Thm_OAI_UniversalTensorSquare_sg25894
import Theorems.Thm_OAI_UniversalTensorSquare_sg25895
import Theorems.Thm_OAI_UniversalTensorSquare_sg25896
import Theorems.Thm_OAI_UniversalTensorSquare_sg25897
import Theorems.Thm_OAI_UniversalTensorSquare_sg25898
import Theorems.Thm_OAI_UniversalTensorSquare_sg25899
import Theorems.Thm_OAI_UniversalTensorSquare_sg25900
import Theorems.Thm_OAI_UniversalTensorSquare_sg25901
import Theorems.Thm_OAI_UniversalTensorSquare_sg25902
import Theorems.Thm_OAI_UniversalTensorSquare_sg8438

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 63. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25890 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8438 sg10230

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

lemma degreeTree43_175All_oai : degreeTree43_175.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25895,⟨sg25891,⟨sg25889,⟨sg25888,True.intro,True.intro⟩,⟨sg25890,True.intro,True.intro⟩⟩,⟨sg25893,⟨sg25892,True.intro,True.intro⟩,⟨sg25894,True.intro,True.intro⟩⟩⟩,⟨sg25899,⟨sg25897,⟨sg25896,True.intro,True.intro⟩,⟨sg25898,True.intro,True.intro⟩⟩,⟨sg25901,⟨sg25900,True.intro,True.intro⟩,⟨sg25902,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_175All_oai := @OAI.UniversalTensorSquare.degreeTree43_175All_oai
