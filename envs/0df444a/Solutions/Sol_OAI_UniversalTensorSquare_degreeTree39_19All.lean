-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree39_19All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T22:45:05.32057+00:00
-- url     : https://prove2.me/submissions/bf197537-da38-442a-9926-520169b43a7a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg21992
import Theorems.Thm_OAI_UniversalTensorSquare_sg21993
import Theorems.Thm_OAI_UniversalTensorSquare_sg21994
import Theorems.Thm_OAI_UniversalTensorSquare_sg21995
import Theorems.Thm_OAI_UniversalTensorSquare_sg21996
import Theorems.Thm_OAI_UniversalTensorSquare_sg21997
import Theorems.Thm_OAI_UniversalTensorSquare_sg21998
import Theorems.Thm_OAI_UniversalTensorSquare_sg22000
import Theorems.Thm_OAI_UniversalTensorSquare_sg22001
import Theorems.Thm_OAI_UniversalTensorSquare_sg22003
import Theorems.Thm_OAI_UniversalTensorSquare_sg22004
import Theorems.Thm_OAI_UniversalTensorSquare_sg22005
import Theorems.Thm_OAI_UniversalTensorSquare_sg22006
import Theorems.Thm_OAI_UniversalTensorSquare_sg22007
import Theorems.Thm_OAI_UniversalTensorSquare_sg22008
import Theorems.Thm_OAI_UniversalTensorSquare_sg22009
import Theorems.Thm_OAI_UniversalTensorSquare_sg22010
import Theorems.Thm_OAI_UniversalTensorSquare_sg22011
import Theorems.Thm_OAI_UniversalTensorSquare_sg22012
import Theorems.Thm_OAI_UniversalTensorSquare_sg22013
import Theorems.Thm_OAI_UniversalTensorSquare_sg22015
import Theorems.Thm_OAI_UniversalTensorSquare_sg22016
import Theorems.Thm_OAI_UniversalTensorSquare_sg22018
import Theorems.Thm_OAI_UniversalTensorSquare_sg3913
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg537
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg6681
import Theorems.Thm_OAI_UniversalTensorSquare_sg6682
import Theorems.Thm_OAI_UniversalTensorSquare_sg6773
import Theorems.Thm_OAI_UniversalTensorSquare_sg7351
import Theorems.Thm_OAI_UniversalTensorSquare_sg7362
import Theorems.Thm_OAI_UniversalTensorSquare_sg910

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

lemma sg4 : RowSquare [2,1] [1,1,1] := by
  have he : rowDiagram [2,1] = (staircase 2) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [2,1]) (rowDiagram [1,1,1])
  have hh : SquareOccurs (staircase 2) (rowDiagram [1,1,1]) :=
    ⟨3,canonicalTableau _ (staircase_card 2),canonicalTableau _ (rowDiagram_card [1,1,1]),
      saxl_kronecker_pos 2 (by decide) _ (rowDiagram_card [1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1])) he) hh

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

lemma sg3964 : RowSquare [5,4,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg586

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6296 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg910

lemma sg6299 : RowSquare [5,5,2,2,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg910

lemma sg6436 : RowSquare [6,5,2,1,1,1,1,1,1] [4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3913

lemma sg6472 : RowSquare [7,5,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3964

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

lemma sg21991 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6299 sg7351

lemma sg21999 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7362

lemma sg22002 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg6436 sg6773

lemma sg22014 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6681

lemma sg22017 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6682

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

lemma degreeTree39_19All_oai : degreeTree39_19.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22005,⟨sg21998,⟨sg21994,⟨sg21992,⟨sg21991,True.intro,True.intro⟩,⟨sg21993,True.intro,True.intro⟩⟩,⟨sg21996,⟨sg21995,True.intro,True.intro⟩,⟨sg21997,True.intro,True.intro⟩⟩⟩,⟨sg22002,⟨sg22000,⟨sg21999,True.intro,True.intro⟩,⟨sg22001,True.intro,True.intro⟩⟩,⟨sg22004,⟨sg22003,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22012,⟨sg22009,⟨sg22007,⟨sg22006,True.intro,True.intro⟩,⟨sg22008,True.intro,True.intro⟩⟩,⟨sg22011,⟨sg22010,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22016,⟨sg22014,⟨sg22013,True.intro,True.intro⟩,⟨sg22015,True.intro,True.intro⟩⟩,⟨sg22018,⟨sg22017,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree39_19All_oai := @OAI.UniversalTensorSquare.degreeTree39_19All_oai
