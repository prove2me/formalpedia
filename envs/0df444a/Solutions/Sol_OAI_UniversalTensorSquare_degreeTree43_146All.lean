-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_146All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T08:05:28.783202+00:00
-- url     : https://prove2.me/submissions/393928ed-8d7e-4145-9cbe-d34620a4acd2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg10260
import Theorems.Thm_OAI_UniversalTensorSquare_sg25548
import Theorems.Thm_OAI_UniversalTensorSquare_sg25549
import Theorems.Thm_OAI_UniversalTensorSquare_sg25550
import Theorems.Thm_OAI_UniversalTensorSquare_sg25551
import Theorems.Thm_OAI_UniversalTensorSquare_sg25552
import Theorems.Thm_OAI_UniversalTensorSquare_sg25553
import Theorems.Thm_OAI_UniversalTensorSquare_sg25554
import Theorems.Thm_OAI_UniversalTensorSquare_sg25555
import Theorems.Thm_OAI_UniversalTensorSquare_sg25556
import Theorems.Thm_OAI_UniversalTensorSquare_sg25557
import Theorems.Thm_OAI_UniversalTensorSquare_sg25558
import Theorems.Thm_OAI_UniversalTensorSquare_sg25559
import Theorems.Thm_OAI_UniversalTensorSquare_sg25560
import Theorems.Thm_OAI_UniversalTensorSquare_sg25561
import Theorems.Thm_OAI_UniversalTensorSquare_sg25562
import Theorems.Thm_OAI_UniversalTensorSquare_sg25563
import Theorems.Thm_OAI_UniversalTensorSquare_sg25564
import Theorems.Thm_OAI_UniversalTensorSquare_sg25565
import Theorems.Thm_OAI_UniversalTensorSquare_sg25566
import Theorems.Thm_OAI_UniversalTensorSquare_sg25567
import Theorems.Thm_OAI_UniversalTensorSquare_sg25568
import Theorems.Thm_OAI_UniversalTensorSquare_sg25569
import Theorems.Thm_OAI_UniversalTensorSquare_sg25570
import Theorems.Thm_OAI_UniversalTensorSquare_sg25571
import Theorems.Thm_OAI_UniversalTensorSquare_sg25572
import Theorems.Thm_OAI_UniversalTensorSquare_sg25573
import Theorems.Thm_OAI_UniversalTensorSquare_sg25574
import Theorems.Thm_OAI_UniversalTensorSquare_sg25576
import Theorems.Thm_OAI_UniversalTensorSquare_sg25577
import Theorems.Thm_OAI_UniversalTensorSquare_sg25578
import Theorems.Thm_OAI_UniversalTensorSquare_sg8425

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25575 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10260

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

lemma degreeTree43_146All_oai : degreeTree43_146.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25563,⟨sg25555,⟨sg25551,⟨sg25549,⟨sg25548,True.intro,True.intro⟩,⟨sg25550,True.intro,True.intro⟩⟩,⟨sg25553,⟨sg25552,True.intro,True.intro⟩,⟨sg25554,True.intro,True.intro⟩⟩⟩,⟨sg25559,⟨sg25557,⟨sg25556,True.intro,True.intro⟩,⟨sg25558,True.intro,True.intro⟩⟩,⟨sg25561,⟨sg25560,True.intro,True.intro⟩,⟨sg25562,True.intro,True.intro⟩⟩⟩⟩,⟨sg25571,⟨sg25567,⟨sg25565,⟨sg25564,True.intro,True.intro⟩,⟨sg25566,True.intro,True.intro⟩⟩,⟨sg25569,⟨sg25568,True.intro,True.intro⟩,⟨sg25570,True.intro,True.intro⟩⟩⟩,⟨sg25575,⟨sg25573,⟨sg25572,True.intro,True.intro⟩,⟨sg25574,True.intro,True.intro⟩⟩,⟨sg25577,⟨sg25576,True.intro,True.intro⟩,⟨sg25578,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_146All_oai := @OAI.UniversalTensorSquare.degreeTree43_146All_oai
