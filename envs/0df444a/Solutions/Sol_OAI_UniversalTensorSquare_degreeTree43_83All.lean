-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_83All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:18:19.390546+00:00
-- url     : https://prove2.me/submissions/455bdcec-3284-4f93-b89f-7fc2b7bcac91
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_82All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1000
import Theorems.Thm_OAI_UniversalTensorSquare_sg10108
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1331
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg21
import Theorems.Thm_OAI_UniversalTensorSquare_sg24708
import Theorems.Thm_OAI_UniversalTensorSquare_sg24709
import Theorems.Thm_OAI_UniversalTensorSquare_sg24710
import Theorems.Thm_OAI_UniversalTensorSquare_sg24712
import Theorems.Thm_OAI_UniversalTensorSquare_sg24713
import Theorems.Thm_OAI_UniversalTensorSquare_sg24714
import Theorems.Thm_OAI_UniversalTensorSquare_sg24715
import Theorems.Thm_OAI_UniversalTensorSquare_sg24716
import Theorems.Thm_OAI_UniversalTensorSquare_sg24718
import Theorems.Thm_OAI_UniversalTensorSquare_sg24719
import Theorems.Thm_OAI_UniversalTensorSquare_sg24720
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg50
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg809
import Theorems.Thm_OAI_UniversalTensorSquare_sg8430
import Theorems.Thm_OAI_UniversalTensorSquare_sg8665
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg998

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

lemma sg105 : RowSquare [5,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg17

lemma sg111 : RowSquare [2,1,1,1,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

lemma sg262 : RowSquare [3,1,1,1,1,1] [4,2,2] := by
  exact rowSquare_join (by decide) sg2 sg89

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

lemma sg912 : RowSquare [5,2,1,1,1] [2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg21

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

lemma sg1338 : RowSquare [6,1,1,1,1,1] [3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg262

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

lemma sg1755 : RowSquare [6,2,1,1,1,1] [2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg50

lemma sg1757 : RowSquare [6,2,1,1,1,1] [2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg111

lemma sg1891 : RowSquare [7,2,2,1] [2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg178

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

lemma sg4742 : RowSquare [5,4,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg998

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

lemma sg8527 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1327

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 21. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8993 : RowSquare [5,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg912 sg1891

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

lemma sg10237 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1331 sg1338

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

lemma sg8722 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg809 sg1327

lemma sg8866 : RowSquare [7,6,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg4742

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

lemma sg9505 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1417 sg1338

lemma sg9668 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1755

lemma sg9669 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg1757

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24711 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9505

lemma sg24717 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8665 sg9668

lemma sg24721 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,4,3,3] := by
  exact rowSquare_join (by decide) sg8665 sg9669

lemma sg24722 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10237

lemma sg24723 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,4,4,2] := by
  exact rowSquare_join (by decide) sg8866 sg8993

lemma sg24724 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8527 sg10108

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

lemma degreeTree43_81All : degreeTree43_81.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24716,⟨sg24712,⟨sg24710,⟨sg24709,⟨sg24708,True.intro,True.intro⟩,True.intro⟩,⟨sg24711,True.intro,True.intro⟩⟩,⟨sg24714,⟨sg24713,True.intro,True.intro⟩,⟨sg24715,True.intro,True.intro⟩⟩⟩,⟨sg24720,⟨sg24718,⟨sg24717,True.intro,True.intro⟩,⟨sg24719,True.intro,True.intro⟩⟩,⟨sg24722,⟨sg24721,True.intro,True.intro⟩,⟨sg24723,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_83All_oai : degreeTree43_83.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24724,degreeTree43_81All,degreeTree43_82All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_83All_oai := @OAI.UniversalTensorSquare.degreeTree43_83All_oai
