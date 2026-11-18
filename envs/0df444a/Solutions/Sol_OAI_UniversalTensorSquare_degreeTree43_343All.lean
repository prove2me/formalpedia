-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_343All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:09:26.399324+00:00
-- url     : https://prove2.me/submissions/34fa936d-883f-4f69-9f48-2a28787d5395
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_342All
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg10214
import Theorems.Thm_OAI_UniversalTensorSquare_sg10215
import Theorems.Thm_OAI_UniversalTensorSquare_sg12669
import Theorems.Thm_OAI_UniversalTensorSquare_sg1682
import Theorems.Thm_OAI_UniversalTensorSquare_sg1815
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg2251
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg28001
import Theorems.Thm_OAI_UniversalTensorSquare_sg28002
import Theorems.Thm_OAI_UniversalTensorSquare_sg28003
import Theorems.Thm_OAI_UniversalTensorSquare_sg28004
import Theorems.Thm_OAI_UniversalTensorSquare_sg28005
import Theorems.Thm_OAI_UniversalTensorSquare_sg28006
import Theorems.Thm_OAI_UniversalTensorSquare_sg28007
import Theorems.Thm_OAI_UniversalTensorSquare_sg28010
import Theorems.Thm_OAI_UniversalTensorSquare_sg28011
import Theorems.Thm_OAI_UniversalTensorSquare_sg28012
import Theorems.Thm_OAI_UniversalTensorSquare_sg28013
import Theorems.Thm_OAI_UniversalTensorSquare_sg28014
import Theorems.Thm_OAI_UniversalTensorSquare_sg28015
import Theorems.Thm_OAI_UniversalTensorSquare_sg28016
import Theorems.Thm_OAI_UniversalTensorSquare_sg28020
import Theorems.Thm_OAI_UniversalTensorSquare_sg28021
import Theorems.Thm_OAI_UniversalTensorSquare_sg28022
import Theorems.Thm_OAI_UniversalTensorSquare_sg28024
import Theorems.Thm_OAI_UniversalTensorSquare_sg28025
import Theorems.Thm_OAI_UniversalTensorSquare_sg28026
import Theorems.Thm_OAI_UniversalTensorSquare_sg28028
import Theorems.Thm_OAI_UniversalTensorSquare_sg28030
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg44
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg5
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg7454
import Theorems.Thm_OAI_UniversalTensorSquare_sg7812
import Theorems.Thm_OAI_UniversalTensorSquare_sg8468
import Theorems.Thm_OAI_UniversalTensorSquare_sg8780
import Theorems.Thm_OAI_UniversalTensorSquare_sg910
import Theorems.Thm_OAI_UniversalTensorSquare_sg958

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

lemma sg16 : RowSquare [3,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg18 : RowSquare [3,1] [3,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg40 : RowSquare [3,2] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg74 : RowSquare [3,2,1] [1,1,1,1,1,1] := by
  have he : rowDiagram [3,2,1] = (staircase 3) := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [3,2,1]) (rowDiagram [1,1,1,1,1,1])
  have hh : SquareOccurs (staircase 3) (rowDiagram [1,1,1,1,1,1]) :=
    ⟨6,canonicalTableau _ (staircase_card 3),canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1]),
      saxl_kronecker_pos 3 (by decide) _ (rowDiagram_card [1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1])) he) hh

lemma sg411 : RowSquare [5,3] [6,1,1] := by
  exact rowSquare_short 3 2 (by decide) (by decide) (by decide)
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

lemma sg53 : RowSquare [2,1,1,1,1] [5,1] := by
  exact rowSquare_join (by decide) sg5 sg7

lemma sg112 : RowSquare [2,1,1,1,1,1] [6,1] := by
  exact rowSquare_join (by decide) sg5 sg20

lemma sg117 : RowSquare [2,2,1,1,1] [4,2,1] := by
  exact rowSquare_join (by decide) sg4 sg18

lemma sg136 : RowSquare [3,1,1,1,1] [4,2,1] := by
  exact rowSquare_join (by decide) sg2 sg34

lemma sg237 : RowSquare [2,1,1,1,1,1,1] [7,1] := by
  exact rowSquare_join (by decide) sg18 sg20

lemma sg264 : RowSquare [3,1,1,1,1,1] [5,2,1] := by
  exact rowSquare_join (by decide) sg7 sg34

lemma sg283 : RowSquare [3,2,1,1,1] [5,2,1] := by
  exact rowSquare_join (by decide) sg0 sg117

lemma sg587 : RowSquare [5,1,1,1,1] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg53

lemma sg609 : RowSquare [5,1,1,1,1] [6,2,1] := by
  exact rowSquare_join (by decide) sg2 sg136

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

lemma sg1328 : RowSquare [6,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg112

lemma sg1371 : RowSquare [6,2,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg910

lemma sg1372 : RowSquare [6,2,1,1,1] [3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg586

lemma sg1462 : RowSquare [6,4,1] [3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg74

lemma sg1474 : RowSquare [6,4,1] [6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg74

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

lemma sg1764 : RowSquare [6,2,1,1,1,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg264

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

lemma sg2252 : RowSquare [7,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg237

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

lemma sg8343 : RowSquare [5,5,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1682

lemma sg8344 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1682

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

lemma sg9159 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1371 sg1371

lemma sg9172 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1371 sg1372

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

lemma sg8831 : RowSquare [7,5,2,1,1,1,1,1,1,1] [5,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg136 sg2702

lemma sg8853 : RowSquare [7,5,2,1,1,1,1,1,1,1] [6,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg283 sg2251

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10704 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [7,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg609 sg2251

lemma sg10741 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1] [8,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg609 sg2252

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11296 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1764

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

lemma sg20940 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1474 sg8780

lemma sg21136 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [8,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg411 sg12669

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

lemma sg17128 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1474 sg7812

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 68. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28008 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1462 sg20940

lemma sg28009 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1815 sg17128

lemma sg28017 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg958 sg21136

lemma sg28018 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,3,3,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10214

lemma sg28019 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,3,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11296

lemma sg28023 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,3,3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10215

lemma sg28027 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,3,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8344 sg10704

lemma sg28029 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,3,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8831 sg9172

lemma sg28031 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,3,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8343 sg10741

lemma sg28032 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,3,3,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8853 sg9159

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

lemma degreeTree43_341All : degreeTree43_341.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28016,⟨sg28008,⟨sg28004,⟨sg28002,⟨sg28001,True.intro,True.intro⟩,⟨sg28003,True.intro,True.intro⟩⟩,⟨sg28006,⟨sg28005,True.intro,True.intro⟩,⟨sg28007,True.intro,True.intro⟩⟩⟩,⟨sg28012,⟨sg28010,⟨sg28009,True.intro,True.intro⟩,⟨sg28011,True.intro,True.intro⟩⟩,⟨sg28014,⟨sg28013,True.intro,True.intro⟩,⟨sg28015,True.intro,True.intro⟩⟩⟩⟩,⟨sg28024,⟨sg28020,⟨sg28018,⟨sg28017,True.intro,True.intro⟩,⟨sg28019,True.intro,True.intro⟩⟩,⟨sg28022,⟨sg28021,True.intro,True.intro⟩,⟨sg28023,True.intro,True.intro⟩⟩⟩,⟨sg28028,⟨sg28026,⟨sg28025,True.intro,True.intro⟩,⟨sg28027,True.intro,True.intro⟩⟩,⟨sg28030,⟨sg28029,True.intro,True.intro⟩,⟨sg28031,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_343All_oai : degreeTree43_343.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28032,degreeTree43_341All,degreeTree43_342All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_343All_oai := @OAI.UniversalTensorSquare.degreeTree43_343All_oai
