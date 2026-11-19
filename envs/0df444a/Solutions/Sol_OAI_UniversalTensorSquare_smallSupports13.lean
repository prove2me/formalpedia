-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupports13
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:28:54.522363+00:00
-- url     : https://prove2.me/submissions/b0b4bd88-fb70-41a5-821b-af1c7d0dba92
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_trivial
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_0
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_1
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_10
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_11
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_12
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_13
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_14
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_15
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_16
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_17
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_18
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_19
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_2
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_20
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_21
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_22
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_23
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_24
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_25
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_26
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_27
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_28
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_29
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_3
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_30
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_31
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_32
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_33
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_34
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_35
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_36
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_37
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_38
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_39
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_4
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_40
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_41
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_42
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_43
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_44
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_45
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_46
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_47
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_48
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_49
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_5
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_50
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_6
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_7
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_8
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport13_9

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 13. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupports13_oai : ∀ q ∈ smallKeys13, RowSquare [4,4,3,2] q := by
  intro q hq
  simp only [smallKeys13, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rowSquare_trivial _ (by decide)
  · exact smallSupport13_0
  · exact smallSupport13_1
  · exact smallSupport13_2
  · exact smallSupport13_3
  · exact smallSupport13_4
  · exact smallSupport13_5
  · exact smallSupport13_6
  · exact smallSupport13_7
  · exact smallSupport13_8
  · exact smallSupport13_9
  · exact smallSupport13_10
  · exact smallSupport13_11
  · exact smallSupport13_12
  · exact smallSupport13_13
  · exact smallSupport13_14
  · exact smallSupport13_15
  · exact smallSupport13_16
  · exact smallSupport13_17
  · exact smallSupport13_18
  · exact smallSupport13_19
  · exact smallSupport13_20
  · exact smallSupport13_21
  · exact smallSupport13_22
  · exact smallSupport13_23
  · exact smallSupport13_24
  · exact smallSupport13_25
  · exact smallSupport13_26
  · exact smallSupport13_27
  · exact smallSupport13_28
  · exact smallSupport13_29
  · exact smallSupport13_30
  · exact smallSupport13_31
  · exact smallSupport13_32
  · exact smallSupport13_33
  · exact smallSupport13_34
  · exact smallSupport13_35
  · exact smallSupport13_36
  · exact smallSupport13_37
  · exact smallSupport13_38
  · exact smallSupport13_39
  · exact smallSupport13_40
  · exact smallSupport13_41
  · exact smallSupport13_42
  · exact smallSupport13_43
  · exact smallSupport13_44
  · exact smallSupport13_45
  · exact smallSupport13_46
  · exact smallSupport13_47
  · exact smallSupport13_48
  · exact smallSupport13_49
  · exact smallSupport13_50

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupports13_oai := @OAI.UniversalTensorSquare.smallSupports13_oai
