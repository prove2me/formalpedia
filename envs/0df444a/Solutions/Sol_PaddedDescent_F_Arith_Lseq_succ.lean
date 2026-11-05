-- Prove2me | solution 1 for PaddedDescent.F.Arith.Lseq_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:57:06.152184+00:00
-- url     : https://prove2.me/submissions/a24e75d4-7f13-4284-943c-bac94a9f9e49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithStack
import Definitions.Def_PaddedDescent_F_ArithCol
import Definitions.Def_PaddedDescent_F_ArithSched

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork PaddedDescent.F.Lists
open PaddedDescent.F.Arith
namespace PaddedDescent.F.Arith
theorem _root_.solution (j : ℕ) : Lseq (j + 1) = Lseq j + Lseq j := by
  rw [Lseq, Lseq, ← add_assoc, pow_succ]; ring
end PaddedDescent.F.Arith
