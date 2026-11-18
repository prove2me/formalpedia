-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree24_21All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:57:17.862902+00:00
-- url     : https://prove2.me/submissions/d0113805-9f8d-4da0-bf92-2210bb22c5a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree24_17All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree24_19All
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg12148
import Theorems.Thm_OAI_UniversalTensorSquare_sg12149
import Theorems.Thm_OAI_UniversalTensorSquare_sg12150
import Theorems.Thm_OAI_UniversalTensorSquare_sg12152
import Theorems.Thm_OAI_UniversalTensorSquare_sg12153
import Theorems.Thm_OAI_UniversalTensorSquare_sg12154
import Theorems.Thm_OAI_UniversalTensorSquare_sg12155
import Theorems.Thm_OAI_UniversalTensorSquare_sg12156
import Theorems.Thm_OAI_UniversalTensorSquare_sg12157
import Theorems.Thm_OAI_UniversalTensorSquare_sg12158
import Theorems.Thm_OAI_UniversalTensorSquare_sg12159
import Theorems.Thm_OAI_UniversalTensorSquare_sg12160
import Theorems.Thm_OAI_UniversalTensorSquare_sg12162
import Theorems.Thm_OAI_UniversalTensorSquare_sg12164
import Theorems.Thm_OAI_UniversalTensorSquare_sg12165
import Theorems.Thm_OAI_UniversalTensorSquare_sg12166
import Theorems.Thm_OAI_UniversalTensorSquare_sg12167
import Theorems.Thm_OAI_UniversalTensorSquare_sg12168
import Theorems.Thm_OAI_UniversalTensorSquare_sg12169
import Theorems.Thm_OAI_UniversalTensorSquare_sg12171
import Theorems.Thm_OAI_UniversalTensorSquare_sg12172
import Theorems.Thm_OAI_UniversalTensorSquare_sg12174
import Theorems.Thm_OAI_UniversalTensorSquare_sg12175
import Theorems.Thm_OAI_UniversalTensorSquare_sg12176
import Theorems.Thm_OAI_UniversalTensorSquare_sg12177
import Theorems.Thm_OAI_UniversalTensorSquare_sg12178
import Theorems.Thm_OAI_UniversalTensorSquare_sg12179
import Theorems.Thm_OAI_UniversalTensorSquare_sg122
import Theorems.Thm_OAI_UniversalTensorSquare_sg2583
import Theorems.Thm_OAI_UniversalTensorSquare_sg2585
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg768
import Theorems.Thm_OAI_UniversalTensorSquare_sg89

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

lemma sg57 : RowSquare [2,2,1,1] [3,2,1] := by
  exact rowSquare_short 2 2 (by decide) (by decide) (by decide)
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

lemma sg150 : RowSquare [3,2,1,1] [4,2,1] := by
  exact rowSquare_join (by decide) sg0 sg57

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

lemma sg766 : RowSquare [3,3,1,1,1,1] [3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg34

lemma sg773 : RowSquare [3,3,1,1,1,1] [4,3,3] := by
  exact rowSquare_join (by decide) sg9 sg89

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

lemma sg2603 : RowSquare [5,4,2,2,1] [3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg150 sg122

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

lemma sg6142 : RowSquare [5,4,2,2,2,2,1,1] [5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg2603

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg12151 : RowSquare [8,6,2,2,2,2,1,1] [7,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg768 sg2583

lemma sg12161 : RowSquare [8,6,2,2,2,2,1,1] [7,6,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg6142

lemma sg12163 : RowSquare [8,6,2,2,2,2,1,1] [7,6,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg766 sg2585

lemma sg12170 : RowSquare [8,6,2,2,2,2,1,1] [7,6,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg768 sg2585

lemma sg12173 : RowSquare [8,6,2,2,2,2,1,1] [7,6,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg773 sg2579

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

lemma degreeTree24_18All : degreeTree24_18.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12164,⟨sg12156,⟨sg12152,⟨sg12150,⟨sg12149,True.intro,True.intro⟩,⟨sg12151,True.intro,True.intro⟩⟩,⟨sg12154,⟨sg12153,True.intro,True.intro⟩,⟨sg12155,True.intro,True.intro⟩⟩⟩,⟨sg12160,⟨sg12158,⟨sg12157,True.intro,True.intro⟩,⟨sg12159,True.intro,True.intro⟩⟩,⟨sg12162,⟨sg12161,True.intro,True.intro⟩,⟨sg12163,True.intro,True.intro⟩⟩⟩⟩,⟨sg12172,⟨sg12168,⟨sg12166,⟨sg12165,True.intro,True.intro⟩,⟨sg12167,True.intro,True.intro⟩⟩,⟨sg12170,⟨sg12169,True.intro,True.intro⟩,⟨sg12171,True.intro,True.intro⟩⟩⟩,⟨sg12176,⟨sg12174,⟨sg12173,True.intro,True.intro⟩,⟨sg12175,True.intro,True.intro⟩⟩,⟨sg12178,⟨sg12177,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_20All : degreeTree24_20.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12179,degreeTree24_18All,degreeTree24_19All⟩

lemma degreeTree24_21All_oai : degreeTree24_21.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12148,degreeTree24_17All,degreeTree24_20All⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree24_21All_oai := @OAI.UniversalTensorSquare.degreeTree24_21All_oai
