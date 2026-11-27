-- Prove2me | solution 1 for TreeStack.F_eq_nonneg_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:13:24.434649+00:00
-- url     : https://prove2.me/submissions/2e410f54-012d-4942-af63-9fa95ae68436

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {z k : ℤ} (hk : 0 ≤ k) :
    F z = k ↔ (0 < k ∧ z = 2 * k) ∨ z = 2 * k + 3 := by
  unfold F
  split_ifs <;> omega
end TreeStack
