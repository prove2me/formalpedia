-- Prove2me | solution 1 for PaddedDescent.F.Arith.Lseq_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:57:12.112744+00:00
-- url     : https://prove2.me/submissions/4e14b8a2-a2f0-41bc-85c0-6bc4cad77390

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
theorem _root_.solution {i j : ℕ} (h : i ≤ j) : Lseq i ≤ Lseq j :=
  Nat.pow_le_pow_right (by norm_num) (by omega)
end PaddedDescent.F.Arith
