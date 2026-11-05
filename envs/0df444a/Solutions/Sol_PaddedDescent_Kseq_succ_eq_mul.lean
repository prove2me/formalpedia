-- Prove2me | solution 1 for PaddedDescent.Kseq_succ_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:18:19.465496+00:00
-- url     : https://prove2.me/submissions/ea243788-4b68-408b-b075-3d7885b27eca

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_Seq
import Theorems.Thm_PaddedDescent_gseq_eq
import Theorems.Thm_PaddedDescent_kseq_succ


set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution (j : ℕ) : Kseq (j + 1) = gseq j * gseq j := by
  rw [gseq_eq, ← pow_add, Kseq, kseq_succ, two_mul]
end PaddedDescent
