-- Prove2me | solution 1 for TreeStack.defect_not_both_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:59:32.827652+00:00
-- url     : https://prove2.me/submissions/dc21d596-1c9f-4323-ab78-88176687eddc

import Mathlib
import Definitions.Def_TreeStack_Obstruction
import Definitions.Def_TreeStack_Defect
import Theorems.Thm_TreeStack_defect_left_nonneg

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a)) :
    ¬ (0 ≤ a ∧ 0 ≤ b) := by
  intro hboth
  have h :=
    defect_left_nonneg hδu hδv ha hb hboth.1
  omega
end TreeStack
