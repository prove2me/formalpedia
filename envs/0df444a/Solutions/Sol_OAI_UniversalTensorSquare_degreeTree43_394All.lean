-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_394All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T00:15:54.534196+00:00
-- url     : https://prove2.me/submissions/470211fa-e382-4ba0-9fbd-472c70da6d03
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg10242
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg28710
import Theorems.Thm_OAI_UniversalTensorSquare_sg28712
import Theorems.Thm_OAI_UniversalTensorSquare_sg28713
import Theorems.Thm_OAI_UniversalTensorSquare_sg28714
import Theorems.Thm_OAI_UniversalTensorSquare_sg28716
import Theorems.Thm_OAI_UniversalTensorSquare_sg28718
import Theorems.Thm_OAI_UniversalTensorSquare_sg28720
import Theorems.Thm_OAI_UniversalTensorSquare_sg28721
import Theorems.Thm_OAI_UniversalTensorSquare_sg28722
import Theorems.Thm_OAI_UniversalTensorSquare_sg28723
import Theorems.Thm_OAI_UniversalTensorSquare_sg28725
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg4161
import Theorems.Thm_OAI_UniversalTensorSquare_sg536
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg6457
import Theorems.Thm_OAI_UniversalTensorSquare_sg8438
import Theorems.Thm_OAI_UniversalTensorSquare_sg8468
import Theorems.Thm_OAI_UniversalTensorSquare_sg982

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert168 : solveCompact 7 (.full [5,1,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,1,1] (Equiv.refl (Fin 7)) sgB168 sgT168) sgFlag168 = 6 := by
  decide +kernel

lemma sg168 : RowSquare [3,3,1] [3,1,1,1,1] := by
  apply rowSquare_compact (n := 7) (cs := [3,2,2]) (ts := [5,1,1])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB168 sgT168 sgFlag168
  change solveCompact 7 (.full [5,1,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [5,1,1] (Equiv.refl (Fin 7)) sgB168 sgT168) sgFlag168 ≠ 0
  rw [sgCert168]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sgCert372 : solveCompact 8 (.full [5,3]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [5,3] (Equiv.refl (Fin 8)) sgB372 sgT372) sgFlag372 = 20 := by
  decide +kernel

lemma sg372 : RowSquare [5,1,1,1] [2,2,2,1,1] := by
  apply rowSquare_compact (n := 8) (cs := [4,1,1,1,1]) (ts := [5,3])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB372 sgT372 sgFlag372
  change solveCompact 8 (.full [5,3]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [5,3] (Equiv.refl (Fin 8)) sgB372 sgT372) sgFlag372 ≠ 0
  rw [sgCert372]
  norm_num

end UniversalTensorSquare
end
end

end OAI
end

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

lemma sg40 : RowSquare [3,2] [2,2,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
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

lemma sg132 : RowSquare [3,1,1,1,1] [3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg32

lemma sg136 : RowSquare [3,1,1,1,1] [4,2,1] := by
  exact rowSquare_join (by decide) sg2 sg34

lemma sg519 : RowSquare [4,1,1,1,1,1] [3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg372

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

lemma sg997 : RowSquare [6,1,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg586

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

lemma sg1352 : RowSquare [6,1,1,1,1,1] [5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg519

lemma sg1401 : RowSquare [6,2,1,1,1] [6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg132

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

lemma sg1852 : RowSquare [6,5,1] [4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg982

lemma sg1861 : RowSquare [6,5,1] [5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg40 sg168

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6909 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1001

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

lemma sg10251 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1352

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9879 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1401

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

lemma sg8651 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg1754

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11479 : RowSquare [7,5,3,2,1,1,1,1,1,1] [6,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg136 sg4161

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

lemma sg16204 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [6,4,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1861 sg6457

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 70. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg28711 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,5,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1852 sg16204

lemma sg28715 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,5,4,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6909 sg11479

lemma sg28717 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,5,4,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8438 sg10251

lemma sg28719 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,5,4,4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10242

lemma sg28724 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,6,5,4,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8651 sg9879

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

lemma degreeTree43_394All_oai : degreeTree43_394.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28718,⟨sg28714,⟨sg28712,⟨sg28711,⟨sg28710,True.intro,True.intro⟩,True.intro⟩,⟨sg28713,True.intro,True.intro⟩⟩,⟨sg28716,⟨sg28715,True.intro,True.intro⟩,⟨sg28717,True.intro,True.intro⟩⟩⟩,⟨sg28722,⟨sg28720,⟨sg28719,True.intro,True.intro⟩,⟨sg28721,True.intro,True.intro⟩⟩,⟨sg28724,⟨sg28723,True.intro,True.intro⟩,⟨sg28725,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_394All_oai := @OAI.UniversalTensorSquare.degreeTree43_394All_oai
