-- Prove2me | solution 1 for PaddedDescent.F.Arith.Inv.st_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:12:29.397793+00:00
-- url     : https://prove2.me/submissions/e2cffa91-18a1-4516-928e-b1a7b93337c1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_ArithLevel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_F_ArithInv
import Theorems.Thm_PaddedDescent_F_Arith_Inv_succ_le
import Theorems.Thm_PaddedDescent_F_Arith_mul_Pn_mul_le
import Theorems.Thm_PaddedDescent_Kseq_pos


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)
variable {t X Z Qm Wm L j lam B cnt : ℕ}
namespace PaddedDescent.F.Arith
namespace Inv
theorem _root_.solution (h : Inv t X Z Qm Wm L (j + 1) lam B cnt) :
    Pn (gseq j) lam * (2 * gseq j / Kseq j) ≤ 4 * (X + Z) := by
  have hK : 0 < Kseq j := Kseq_pos j
  refine Nat.le_of_mul_le_mul_left ?_ hK
  calc Kseq j * (Pn (gseq j) lam * (2 * gseq j / Kseq j)) ≤ 4 * (gseq j ^ 4 * lam) := mul_Pn_mul_le _ _ _
    _ ≤ 4 * (Kseq j * (X + Z)) := Nat.mul_le_mul_left _ h.succ_le
    _ = Kseq j * (4 * (X + Z)) := by ring
end Inv
end PaddedDescent.F.Arith
