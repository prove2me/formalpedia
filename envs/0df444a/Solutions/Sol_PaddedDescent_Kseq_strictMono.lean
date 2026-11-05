-- Prove2me | solution 1 for PaddedDescent.Kseq_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:51:58.097119+00:00
-- url     : https://prove2.me/submissions/ed51a42a-3aca-495e-8f92-16c8a19b3ba4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_Seq
import Theorems.Thm_PaddedDescent_kseq_strictMono__cf83c2

set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution : StrictMono Kseq := fun _ _ h =>
  Nat.pow_lt_pow_right (by norm_num) (kseq_strictMono h)
end PaddedDescent
