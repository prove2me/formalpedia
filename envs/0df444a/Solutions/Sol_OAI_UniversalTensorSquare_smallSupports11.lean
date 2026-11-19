-- Prove2me | solution 1 for OAI.UniversalTensorSquare.smallSupports11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:28:48.66823+00:00
-- url     : https://prove2.me/submissions/c1b74023-c8e6-4266-a59c-3eeb2be6166b

import Mathlib
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US007
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_trivial
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_0
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_1
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_10
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_11
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_12
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_13
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_14
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_15
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_16
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_17
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_18
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_19
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_2
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_20
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_21
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_22
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_23
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_24
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_25
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_26
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_27
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_3
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_4
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_5
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_6
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_7
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_8
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupport11_9

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallSupports11_oai : ∀ q ∈ smallKeys11, RowSquare [4,3,3,1] q := by
  intro q hq
  simp only [smallKeys11, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rowSquare_trivial _ (by decide)
  · exact smallSupport11_0
  · exact smallSupport11_1
  · exact smallSupport11_2
  · exact smallSupport11_3
  · exact smallSupport11_4
  · exact smallSupport11_5
  · exact smallSupport11_6
  · exact smallSupport11_7
  · exact smallSupport11_8
  · exact smallSupport11_9
  · exact smallSupport11_10
  · exact smallSupport11_11
  · exact smallSupport11_12
  · exact smallSupport11_13
  · exact smallSupport11_14
  · exact smallSupport11_15
  · exact smallSupport11_16
  · exact smallSupport11_17
  · exact smallSupport11_18
  · exact smallSupport11_19
  · exact smallSupport11_20
  · exact smallSupport11_21
  · exact smallSupport11_22
  · exact smallSupport11_23
  · exact smallSupport11_24
  · exact smallSupport11_25
  · exact smallSupport11_26
  · exact smallSupport11_27

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.smallSupports11_oai := @OAI.UniversalTensorSquare.smallSupports11_oai
