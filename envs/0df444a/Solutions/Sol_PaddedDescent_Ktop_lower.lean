-- Prove2me | solution 1 for PaddedDescent.Ktop_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:17:25.639576+00:00
-- url     : https://prove2.me/submissions/74f48064-a339-4482-a42e-365cd6d98527

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_Seq
import Theorems.Thm_PaddedDescent_kseq_ge__b51875

set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution (s : ℕ) : 2 ^ (52 * s + 692) ≤ Ktop s := by
  have h := kseq_ge (depthOf s)
  rw [Ktop, Kseq]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  unfold depthOf at h ⊢
  omega
end PaddedDescent
