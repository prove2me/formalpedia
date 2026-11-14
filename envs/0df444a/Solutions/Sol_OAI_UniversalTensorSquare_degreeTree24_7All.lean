-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree24_7All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T21:00:11.470198+00:00
-- url     : https://prove2.me/submissions/09234486-207d-4e65-8abf-bc5af821ef33
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_compact
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg11964
import Theorems.Thm_OAI_UniversalTensorSquare_sg11965
import Theorems.Thm_OAI_UniversalTensorSquare_sg11966
import Theorems.Thm_OAI_UniversalTensorSquare_sg11967
import Theorems.Thm_OAI_UniversalTensorSquare_sg11968
import Theorems.Thm_OAI_UniversalTensorSquare_sg11969
import Theorems.Thm_OAI_UniversalTensorSquare_sg11970
import Theorems.Thm_OAI_UniversalTensorSquare_sg11971
import Theorems.Thm_OAI_UniversalTensorSquare_sg11972
import Theorems.Thm_OAI_UniversalTensorSquare_sg11973
import Theorems.Thm_OAI_UniversalTensorSquare_sg11975
import Theorems.Thm_OAI_UniversalTensorSquare_sg11976
import Theorems.Thm_OAI_UniversalTensorSquare_sg11977
import Theorems.Thm_OAI_UniversalTensorSquare_sg11978
import Theorems.Thm_OAI_UniversalTensorSquare_sg11979
import Theorems.Thm_OAI_UniversalTensorSquare_sg11980
import Theorems.Thm_OAI_UniversalTensorSquare_sg11981
import Theorems.Thm_OAI_UniversalTensorSquare_sg11983
import Theorems.Thm_OAI_UniversalTensorSquare_sg11984
import Theorems.Thm_OAI_UniversalTensorSquare_sg11985
import Theorems.Thm_OAI_UniversalTensorSquare_sg11986
import Theorems.Thm_OAI_UniversalTensorSquare_sg11987
import Theorems.Thm_OAI_UniversalTensorSquare_sg11988
import Theorems.Thm_OAI_UniversalTensorSquare_sg11989
import Theorems.Thm_OAI_UniversalTensorSquare_sg11990
import Theorems.Thm_OAI_UniversalTensorSquare_sg11992
import Theorems.Thm_OAI_UniversalTensorSquare_sg11993
import Theorems.Thm_OAI_UniversalTensorSquare_sg178
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg586

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

lemma sgCert88 : solveCompact 6 (.full [4,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [4,2] (Equiv.refl (Fin 6)) sgB88 sgT88) sgFlag88 = 8 := by
  decide +kernel

lemma sg88 : RowSquare [4,1,1] [2,2,1,1] := by
  apply rowSquare_compact (n := 6) (cs := [3,1,1,1]) (ts := [4,2])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl rfl sgB88 sgT88 sgFlag88
  change solveCompact 6 (.full [4,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [4,2] (Equiv.refl (Fin 6)) sgB88 sgT88) sgFlag88 ≠ 0
  rw [sgCert88]
  norm_num

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

lemma sg87 : RowSquare [4,1,1] [2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg32

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

lemma sg762 : RowSquare [3,3,1,1,1,1] [2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg32

lemma sg764 : RowSquare [3,3,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg33

lemma sg1205 : RowSquare [4,3,1,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg762

lemma sg1206 : RowSquare [4,3,1,1,1,1] [3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg178

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

lemma sg2039 : RowSquare [4,3,1,1,1,1,1,1] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg87 sg178

lemma sg2040 : RowSquare [4,3,1,1,1,1,1,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg88 sg178

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

lemma sg2579 : RowSquare [5,3,1,1,1,1,1,1] [3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg34 sg586

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

lemma sg11974 : RowSquare [8,6,2,2,2,2,1,1] [6,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1206 sg2039

lemma sg11982 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg764 sg2579

lemma sg11991 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1205 sg2040

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

lemma degreeTree24_7All_oai : degreeTree24_7.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg11979,⟨sg11971,⟨sg11967,⟨sg11965,⟨sg11964,True.intro,True.intro⟩,⟨sg11966,True.intro,True.intro⟩⟩,⟨sg11969,⟨sg11968,True.intro,True.intro⟩,⟨sg11970,True.intro,True.intro⟩⟩⟩,⟨sg11975,⟨sg11973,⟨sg11972,True.intro,True.intro⟩,⟨sg11974,True.intro,True.intro⟩⟩,⟨sg11977,⟨sg11976,True.intro,True.intro⟩,⟨sg11978,True.intro,True.intro⟩⟩⟩⟩,⟨sg11987,⟨sg11983,⟨sg11981,⟨sg11980,True.intro,True.intro⟩,⟨sg11982,True.intro,True.intro⟩⟩,⟨sg11985,⟨sg11984,True.intro,True.intro⟩,⟨sg11986,True.intro,True.intro⟩⟩⟩,⟨sg11991,⟨sg11989,⟨sg11988,True.intro,True.intro⟩,⟨sg11990,True.intro,True.intro⟩⟩,⟨sg11993,⟨sg11992,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree24_7All_oai := @OAI.UniversalTensorSquare.degreeTree24_7All_oai
