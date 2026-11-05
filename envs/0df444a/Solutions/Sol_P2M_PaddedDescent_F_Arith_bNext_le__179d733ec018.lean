-- Prove2me | solution 1 for P2M_PaddedDescent_F_Arith_bNext_le__179d733ec018
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:30.623094+00:00
-- url     : https://prove2.me/submissions/f3bf5b74-bee3-4784-8817-5df028ac8845

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithLevel
import Theorems.Thm_PaddedDescent_F_Arith_bNext_le

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {K g : ℕ} (hK : 256 ≤ K) (hg : K ≤ g) (lam B : ℕ) :
    bNext K g lam B ≤ 6 * (g ^ 3 * B) + 8 * (g ^ 4 * lam) := by
  have h := bNext_le hK hg lam B
  omega
end PaddedDescent.F.Arith
