-- Prove2me | solution 1 for PaddedDescent.F.Arith.lt_two_pow_Lof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:04:49.870518+00:00
-- url     : https://prove2.me/submissions/8722ad8f-514c-4aa6-a688-aee53139c943

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution (s n : ℕ) : n < 2 ^ Lof s n :=
  lt_of_lt_of_le (Nat.lt_size_self n) (Nat.pow_le_pow_right (by norm_num) (by unfold Lof; omega))
end PaddedDescent.F.Arith
