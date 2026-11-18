-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree24_8All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:57:26.315856+00:00
-- url     : https://prove2.me/submissions/5d8ac13d-8c1e-4221-9667-c4a2146591ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg11995
import Theorems.Thm_OAI_UniversalTensorSquare_sg11997
import Theorems.Thm_OAI_UniversalTensorSquare_sg120
import Theorems.Thm_OAI_UniversalTensorSquare_sg12000
import Theorems.Thm_OAI_UniversalTensorSquare_sg12001
import Theorems.Thm_OAI_UniversalTensorSquare_sg12002
import Theorems.Thm_OAI_UniversalTensorSquare_sg12003
import Theorems.Thm_OAI_UniversalTensorSquare_sg12004
import Theorems.Thm_OAI_UniversalTensorSquare_sg12005
import Theorems.Thm_OAI_UniversalTensorSquare_sg12006
import Theorems.Thm_OAI_UniversalTensorSquare_sg12007
import Theorems.Thm_OAI_UniversalTensorSquare_sg12008
import Theorems.Thm_OAI_UniversalTensorSquare_sg12010
import Theorems.Thm_OAI_UniversalTensorSquare_sg12011
import Theorems.Thm_OAI_UniversalTensorSquare_sg12012
import Theorems.Thm_OAI_UniversalTensorSquare_sg12013
import Theorems.Thm_OAI_UniversalTensorSquare_sg12014
import Theorems.Thm_OAI_UniversalTensorSquare_sg12015
import Theorems.Thm_OAI_UniversalTensorSquare_sg12017
import Theorems.Thm_OAI_UniversalTensorSquare_sg12018
import Theorems.Thm_OAI_UniversalTensorSquare_sg12019
import Theorems.Thm_OAI_UniversalTensorSquare_sg12020
import Theorems.Thm_OAI_UniversalTensorSquare_sg12021
import Theorems.Thm_OAI_UniversalTensorSquare_sg12023
import Theorems.Thm_OAI_UniversalTensorSquare_sg12024
import Theorems.Thm_OAI_UniversalTensorSquare_sg122
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg509
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg768
import Theorems.Thm_OAI_UniversalTensorSquare_sg774
import Theorems.Thm_OAI_UniversalTensorSquare_sg89

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

lemma sgCert17 : solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB17 sgT17) sgFlag17 = -2 := by
  decide +kernel

lemma sg17 : RowSquare [3,1] [2,2] := by
  apply rowSquare_compact (n := 4) (cs := [2,1,1]) (ts := [2,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB17 sgT17 sgFlag17
  change solveCompact 4 (.full [2,2]) (.full [2,1,1]) (.full [2,1,1])
    (certificateEdges [2,1,1] [2,1,1] [2,2] (Equiv.refl (Fin 4)) sgB17 sgT17) sgFlag17 ≠ 0
  rw [sgCert17]
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

lemma sg9 : RowSquare [2,1,1] [2,1,1] := by
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

lemma sg23 : RowSquare [2,1,1,1] [3,2] := by
  exact rowSquare_join (by decide) sg0 sg17

lemma sg152 : RowSquare [3,2,1,1] [5,2] := by
  exact rowSquare_join (by decide) sg1 sg23

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

lemma sg773 : RowSquare [3,3,1,1,1,1] [4,3,3] := by
  exact rowSquare_join (by decide) sg9 sg89

lemma sg1203 : RowSquare [4,3,1,1,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg178

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

lemma sg2042 : RowSquare [4,3,1,1,1,1,1,1] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg178

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

lemma sg2576 : RowSquare [5,3,1,1,1,1,1,1] [2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg586

lemma sg2577 : RowSquare [5,3,1,1,1,1,1,1] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg586

lemma sg2598 : RowSquare [5,4,2,2,1] [2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg152 sg122

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

lemma sg4000 : RowSquare [5,5,2,2,2] [2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg120 sg509

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

lemma sg6134 : RowSquare [5,4,2,2,2,2,1,1] [4,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg2598

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7263 : RowSquare [5,5,2,2,2,2,1,1] [4,4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg4000

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 28. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11996 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg773 sg2576

lemma sg11998 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1203 sg2042

lemma sg11999 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg768 sg2577

lemma sg12009 : RowSquare [8,6,2,2,2,2,1,1] [6,6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7263

lemma sg12016 : RowSquare [8,6,2,2,2,2,1,1] [6,6,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg6134

lemma sg12022 : RowSquare [8,6,2,2,2,2,1,1] [6,6,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg774 sg2576

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree24_8All_oai : degreeTree24_8.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12010,⟨sg12002,⟨sg11998,⟨sg11996,⟨sg11995,True.intro,True.intro⟩,⟨sg11997,True.intro,True.intro⟩⟩,⟨sg12000,⟨sg11999,True.intro,True.intro⟩,⟨sg12001,True.intro,True.intro⟩⟩⟩,⟨sg12006,⟨sg12004,⟨sg12003,True.intro,True.intro⟩,⟨sg12005,True.intro,True.intro⟩⟩,⟨sg12008,⟨sg12007,True.intro,True.intro⟩,⟨sg12009,True.intro,True.intro⟩⟩⟩⟩,⟨sg12018,⟨sg12014,⟨sg12012,⟨sg12011,True.intro,True.intro⟩,⟨sg12013,True.intro,True.intro⟩⟩,⟨sg12016,⟨sg12015,True.intro,True.intro⟩,⟨sg12017,True.intro,True.intro⟩⟩⟩,⟨sg12022,⟨sg12020,⟨sg12019,True.intro,True.intro⟩,⟨sg12021,True.intro,True.intro⟩⟩,⟨sg12024,⟨sg12023,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree24_8All_oai := @OAI.UniversalTensorSquare.degreeTree24_8All_oai
