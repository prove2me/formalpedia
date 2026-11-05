-- Prove2me | solution 1 for PaddedDescent.two_pow_le_Ktop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:54:59.987259+00:00
-- url     : https://prove2.me/submissions/7f440188-8bca-45fc-ac14-b5a6ba4de4d1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_Seq
import Theorems.Thm_PaddedDescent_two_pow_le_kseq

set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution {e s : ℕ} (h : e ≤ 2 ^ depthOf s) : 2 ^ e ≤ Ktop s := by
  rw [Ktop, Kseq]
  exact Nat.pow_le_pow_right (by norm_num) (h.trans (two_pow_le_kseq _))
end PaddedDescent
