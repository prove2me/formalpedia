-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_144All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:12:21.360868+00:00
-- url     : https://prove2.me/submissions/5471078d-a1fd-410c-8d83-dbd0255a89b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg25516
import Theorems.Thm_OAI_UniversalTensorSquare_sg25517
import Theorems.Thm_OAI_UniversalTensorSquare_sg25518
import Theorems.Thm_OAI_UniversalTensorSquare_sg25519
import Theorems.Thm_OAI_UniversalTensorSquare_sg25520
import Theorems.Thm_OAI_UniversalTensorSquare_sg25521
import Theorems.Thm_OAI_UniversalTensorSquare_sg25522
import Theorems.Thm_OAI_UniversalTensorSquare_sg25523
import Theorems.Thm_OAI_UniversalTensorSquare_sg25524
import Theorems.Thm_OAI_UniversalTensorSquare_sg25525
import Theorems.Thm_OAI_UniversalTensorSquare_sg25526
import Theorems.Thm_OAI_UniversalTensorSquare_sg25527
import Theorems.Thm_OAI_UniversalTensorSquare_sg25528
import Theorems.Thm_OAI_UniversalTensorSquare_sg25529
import Theorems.Thm_OAI_UniversalTensorSquare_sg25530
import Theorems.Thm_OAI_UniversalTensorSquare_sg25532
import Theorems.Thm_OAI_UniversalTensorSquare_sg25533
import Theorems.Thm_OAI_UniversalTensorSquare_sg25534
import Theorems.Thm_OAI_UniversalTensorSquare_sg25535
import Theorems.Thm_OAI_UniversalTensorSquare_sg25536
import Theorems.Thm_OAI_UniversalTensorSquare_sg25537
import Theorems.Thm_OAI_UniversalTensorSquare_sg25538
import Theorems.Thm_OAI_UniversalTensorSquare_sg25539
import Theorems.Thm_OAI_UniversalTensorSquare_sg25540
import Theorems.Thm_OAI_UniversalTensorSquare_sg25541
import Theorems.Thm_OAI_UniversalTensorSquare_sg25542
import Theorems.Thm_OAI_UniversalTensorSquare_sg25543
import Theorems.Thm_OAI_UniversalTensorSquare_sg25544
import Theorems.Thm_OAI_UniversalTensorSquare_sg25545
import Theorems.Thm_OAI_UniversalTensorSquare_sg25546
import Theorems.Thm_OAI_UniversalTensorSquare_sg8648
import Theorems.Thm_OAI_UniversalTensorSquare_sg9797

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

lemma sg25531 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9797

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

lemma degreeTree43_144All_oai : degreeTree43_144.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25531,⟨sg25523,⟨sg25519,⟨sg25517,⟨sg25516,True.intro,True.intro⟩,⟨sg25518,True.intro,True.intro⟩⟩,⟨sg25521,⟨sg25520,True.intro,True.intro⟩,⟨sg25522,True.intro,True.intro⟩⟩⟩,⟨sg25527,⟨sg25525,⟨sg25524,True.intro,True.intro⟩,⟨sg25526,True.intro,True.intro⟩⟩,⟨sg25529,⟨sg25528,True.intro,True.intro⟩,⟨sg25530,True.intro,True.intro⟩⟩⟩⟩,⟨sg25539,⟨sg25535,⟨sg25533,⟨sg25532,True.intro,True.intro⟩,⟨sg25534,True.intro,True.intro⟩⟩,⟨sg25537,⟨sg25536,True.intro,True.intro⟩,⟨sg25538,True.intro,True.intro⟩⟩⟩,⟨sg25543,⟨sg25541,⟨sg25540,True.intro,True.intro⟩,⟨sg25542,True.intro,True.intro⟩⟩,⟨sg25545,⟨sg25544,True.intro,True.intro⟩,⟨sg25546,True.intro,True.intro⟩⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_144All_oai := @OAI.UniversalTensorSquare.degreeTree43_144All_oai
