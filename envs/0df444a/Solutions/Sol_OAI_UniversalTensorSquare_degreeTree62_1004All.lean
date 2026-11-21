-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree62_1004All
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T14:06:32.869057+00:00
-- url     : https://prove2.me/submissions/9a62df82-3305-449b-99cd-96cb40e828c8

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree62_1003All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1001
import Theorems.Thm_OAI_UniversalTensorSquare_sg1033
import Theorems.Thm_OAI_UniversalTensorSquare_sg108
import Theorems.Thm_OAI_UniversalTensorSquare_sg1327
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg18912
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg20
import Theorems.Thm_OAI_UniversalTensorSquare_sg2702
import Theorems.Thm_OAI_UniversalTensorSquare_sg271
import Theorems.Thm_OAI_UniversalTensorSquare_sg3
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg43059
import Theorems.Thm_OAI_UniversalTensorSquare_sg43060
import Theorems.Thm_OAI_UniversalTensorSquare_sg43061
import Theorems.Thm_OAI_UniversalTensorSquare_sg43065
import Theorems.Thm_OAI_UniversalTensorSquare_sg43066
import Theorems.Thm_OAI_UniversalTensorSquare_sg43067
import Theorems.Thm_OAI_UniversalTensorSquare_sg43068
import Theorems.Thm_OAI_UniversalTensorSquare_sg43071
import Theorems.Thm_OAI_UniversalTensorSquare_sg43072
import Theorems.Thm_OAI_UniversalTensorSquare_sg43073
import Theorems.Thm_OAI_UniversalTensorSquare_sg43074
import Theorems.Thm_OAI_UniversalTensorSquare_sg43075
import Theorems.Thm_OAI_UniversalTensorSquare_sg43076
import Theorems.Thm_OAI_UniversalTensorSquare_sg43077
import Theorems.Thm_OAI_UniversalTensorSquare_sg43079
import Theorems.Thm_OAI_UniversalTensorSquare_sg43080
import Theorems.Thm_OAI_UniversalTensorSquare_sg49
import Theorems.Thm_OAI_UniversalTensorSquare_sg516
import Theorems.Thm_OAI_UniversalTensorSquare_sg52
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg7

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

lemma sgCert10 : solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB10 sgT10) sgFlag10 = -2 := by
  decide +kernel

lemma sg10 : RowSquare [2,1,1] [2,2] := by
  apply rowSquare_compact (n := 4) (cs := [2,1,1]) (ts := [2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB10 sgT10 sgFlag10
  change solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB10 sgT10) sgFlag10 ≠ 0
  rw [sgCert10]
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

lemma sgCert490 : solveCompact 9 (.full [5,4]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB490 sgT490) sgFlag490 = 2 := by
  decide +kernel

lemma sg490 : RowSquare [3,3,1,1,1] [2,2,2,2,1] := by
  apply rowSquare_compact (n := 9) (cs := [3,3,1,1,1]) (ts := [5,4])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB490 sgT490 sgFlag490
  change solveCompact 9 (.full [5,4]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB490 sgT490) sgFlag490 ≠ 0
  rw [sgCert490]
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

lemma sg26 : RowSquare [2,2,1] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg30 : RowSquare [2,2,1] [4,1] := by
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

lemma sg105 : RowSquare [5,1] [4,2] := by
  exact rowSquare_join (by decide) sg2 sg17

lemma sg307 : RowSquare [3,3,2] [2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3 sg30

lemma sg430 : RowSquare [2,1,1,1,1,1,1,1] [8,1] := by
  exact rowSquare_join (by decide) sg18 sg49

lemma sg494 : RowSquare [3,3,1,1,1] [3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg32

lemma sg588 : RowSquare [5,1,1,1,1] [2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg52

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

lemma sg1502 : RowSquare [7,1,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg1001

lemma sg1504 : RowSquare [7,1,1,1,1] [4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg588

lemma sg1552 : RowSquare [8,1,1,1] [5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg178

lemma sg1553 : RowSquare [8,1,1,1] [5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg371

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

lemma sg1950 : RowSquare [8,1,1,1,1] [5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg588

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

lemma sg2214 : RowSquare [6,4,3] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg307

lemma sg2216 : RowSquare [6,4,3] [3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg516

lemma sg2457 : RowSquare [9,2,1,1] [5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg7 sg1033

lemma sg2458 : RowSquare [9,2,1,1] [5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg178

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

lemma sg4023 : RowSquare [6,3,1,1,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1327

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

lemma sg3375 : RowSquare [7,2,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2702

lemma sg3522 : RowSquare [8,1,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg108 sg430

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12808 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2216 sg2457

lemma sg12809 : RowSquare [4,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2214 sg2458

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

lemma sg11236 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1504 sg1950

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

lemma sg8947 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1552 sg1502

lemma sg8970 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1504 sg1553

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

lemma sg20265 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg271 sg11236

lemma sg20267 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg490 sg8970

lemma sg20269 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [11,6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg494 sg8947

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

lemma sg20631 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3375 sg4023

lemma sg20632 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3964

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

lemma sg17077 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12808

lemma sg17078 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12809

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 106. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg43062 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [14,9,7,7,5,5,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20265

lemma sg43063 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [14,9,7,7,6,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg17078

lemma sg43064 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [14,9,7,7,6,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17077

lemma sg43069 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [14,9,7,7,6,5,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20267

lemma sg43070 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [14,9,7,7,6,5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17078

lemma sg43078 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [14,9,7,7,7,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20269

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

lemma degreeTree62_1002All : degreeTree62_1002.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43069,⟨sg43064,⟨sg43061,⟨sg43060,⟨sg43059,True.intro,True.intro⟩,True.intro⟩,⟨sg43063,⟨sg43062,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43067,⟨sg43066,⟨sg43065,True.intro,True.intro⟩,True.intro⟩,⟨sg43068,True.intro,True.intro⟩⟩⟩,⟨sg43075,⟨sg43072,⟨sg43071,⟨sg43070,True.intro,True.intro⟩,True.intro⟩,⟨sg43074,⟨sg43073,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43078,⟨sg43077,⟨sg43076,True.intro,True.intro⟩,True.intro⟩,⟨sg43079,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_1004All_oai : degreeTree62_1004.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43080,degreeTree62_1002All,degreeTree62_1003All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree62_1004All_oai := @OAI.UniversalTensorSquare.degreeTree62_1004All_oai
