-- Prove2me | solution 1 for TreeStack.defect_edge_classification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:02:02.111882+00:00
-- url     : https://prove2.me/submissions/59673fe5-9b0a-44c3-9450-4003dd723958

import Mathlib
import Definitions.Def_TreeStack_Obstruction
import Definitions.Def_TreeStack_Defect
import Theorems.Thm_TreeStack_defect_left_nonneg
import Theorems.Thm_TreeStack_defect_right_nonneg
import Theorems.Thm_TreeStack_defect_two_negative

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a)) :
    (0 ≤ a ∧
      b = -2 * (a + δv) - 3 ∧
      (δu = 2 * δv ∨
        (0 < a ∧ δu = 2 * δv + 3))) ∨
    (0 ≤ b ∧
      a = -2 * (b + δu) - 3 ∧
      (δv = 2 * δu ∨
        (0 < b ∧ δv = 2 * δu + 3))) ∨
    ∃ r q : ℤ,
      0 ≤ r ∧ 0 ≤ q ∧
      a = -(2 * r + 1) ∧
      b = -(2 * q + 1) ∧
      δu = r + 2 * q ∧
      δv = q + 2 * r := by
  by_cases ha0 : 0 ≤ a
  · left
    exact ⟨ha0, defect_left_nonneg hδu hδv ha hb ha0⟩
  · have haNeg : a < 0 := by
      omega
    by_cases hb0 : 0 ≤ b
    · right
      left
      exact ⟨hb0, defect_right_nonneg hδu hδv ha hb hb0⟩
    · have hbNeg : b < 0 := by
        omega
      right
      right
      exact defect_two_negative hδu hδv ha hb haNeg hbNeg
end TreeStack
