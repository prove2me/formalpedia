-- Prove2me | solution 1 for PaddedDescent.two_pow_mul_Kseq_le_gseq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:17:52.596398+00:00
-- url     : https://prove2.me/submissions/4717e00d-b2f5-4a25-b34e-48f73805e217

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_Seq

set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution (j : ℕ) : 2 ^ 47 * Kseq j ≤ gseq j := by
  rw [gseq, Lseq, mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
end PaddedDescent
