-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_57All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:10:16.13605+00:00
-- url     : https://prove2.me/submissions/2970a92f-54e2-4e74-8bfc-33427d772337
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US011
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg1023
import Theorems.Thm_OAI_UniversalTensorSquare_sg16654
import Theorems.Thm_OAI_UniversalTensorSquare_sg16689
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg32687
import Theorems.Thm_OAI_UniversalTensorSquare_sg32689
import Theorems.Thm_OAI_UniversalTensorSquare_sg32690
import Theorems.Thm_OAI_UniversalTensorSquare_sg32691
import Theorems.Thm_OAI_UniversalTensorSquare_sg32692
import Theorems.Thm_OAI_UniversalTensorSquare_sg32693
import Theorems.Thm_OAI_UniversalTensorSquare_sg32694
import Theorems.Thm_OAI_UniversalTensorSquare_sg32695
import Theorems.Thm_OAI_UniversalTensorSquare_sg32696
import Theorems.Thm_OAI_UniversalTensorSquare_sg32697
import Theorems.Thm_OAI_UniversalTensorSquare_sg32699
import Theorems.Thm_OAI_UniversalTensorSquare_sg32700
import Theorems.Thm_OAI_UniversalTensorSquare_sg32702
import Theorems.Thm_OAI_UniversalTensorSquare_sg32704
import Theorems.Thm_OAI_UniversalTensorSquare_sg32705
import Theorems.Thm_OAI_UniversalTensorSquare_sg32706
import Theorems.Thm_OAI_UniversalTensorSquare_sg4842
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg4949
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg703
import Theorems.Thm_OAI_UniversalTensorSquare_sg809
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg92

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

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg232 : RowSquare [6,1] [5,2] := by
  exact rowSquare_join (by decide) sg7 sg17

lemma sg429 : RowSquare [2,1,1,1,1,1,1,1] [7,2] := by
  exact rowSquare_join (by decide) sg17 sg49

lemma sg430 : RowSquare [2,1,1,1,1,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg18 sg49

lemma sg451 : RowSquare [3,1,1,1,1,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg7 sg92

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

lemma sg741 : RowSquare [3,2,1,1,1,1,1] [4,4,2] := by
  exact rowSquare_join (by decide) sg17 sg89

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

lemma sg2546 : RowSquare [4,4,1,1,1,1,1,1] [2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg178

lemma sg2707 : RowSquare [7,2,1,1,1,1,1] [2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg451

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3258 : RowSquare [5,3,1,1,1,1,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg1001

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

lemma sg5737 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg703 sg430

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

lemma sg3316 : RowSquare [6,3,2,1,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg809

lemma sg3404 : RowSquare [7,3,2,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg809

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

lemma sg4173 : RowSquare [7,3,2,1,1,1,1] [3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg89 sg741

lemma sg4348 : RowSquare [8,2,1,1,1,1,1,1] [2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg232 sg429

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 36. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15102 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg4949

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

lemma sg15615 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1] [6,6,6,6,6] := by
  exact rowSquare_join (by decide) sg3404 sg3316

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

lemma sg20636 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2546 sg4933

lemma sg20653 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3258 sg4348

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

lemma sg21050 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2707 sg5737

lemma sg21200 : RowSquare [9,7,3,3,2,2,1,1,1,1,1,1,1] [6,6,6,6,5,4] := by
  exact rowSquare_join (by decide) sg4173 sg4842

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 80. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg32688 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,9,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20653 sg16654

lemma sg32698 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,9,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16689

lemma sg32701 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,9,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15102 sg21200

lemma sg32703 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,10,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15615 sg21050

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

lemma degreeTree62_57All_oai : degreeTree62_57.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32697,⟨sg32692,⟨sg32689,⟨sg32688,⟨sg32687,True.intro,True.intro⟩,True.intro⟩,⟨sg32691,⟨sg32690,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32695,⟨sg32694,⟨sg32693,True.intro,True.intro⟩,True.intro⟩,⟨sg32696,True.intro,True.intro⟩⟩⟩,⟨sg32702,⟨sg32700,⟨sg32699,⟨sg32698,True.intro,True.intro⟩,True.intro⟩,⟨sg32701,True.intro,True.intro⟩⟩,⟨sg32705,⟨sg32704,⟨sg32703,True.intro,True.intro⟩,True.intro⟩,⟨sg32706,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_57All_oai := @OAI.UniversalTensorSquare.degreeTree62_57All_oai
