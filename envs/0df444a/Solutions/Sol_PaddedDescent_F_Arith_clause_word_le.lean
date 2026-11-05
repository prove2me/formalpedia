-- Prove2me | solution 1 for PaddedDescent.F.Arith.clause_word_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:04:38.043251+00:00
-- url     : https://prove2.me/submissions/0a50743f-db81-4dce-8082-d33b4c9f64be

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_Threshold
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_PaddedDescent_F_ArithStack

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork Groundwork.Sparsify PaddedDescent.F.Lists
open WidthK (theta bsum)
open WidthK.Prog (stepK)
namespace PaddedDescent.F.Arith
theorem _root_.solution {k n a : ℕ} (hn : n < a) (hk : k < a) (ha : 4 ≤ a) : k * (3 * n + 5) + 10 ≤ a ^ 3 := by
  have h1 : 3 * n + 5 ≤ a * a := by nlinarith
  have h2 : 10 ≤ a * a := by nlinarith
  calc k * (3 * n + 5) + 10 ≤ k * (a * a) + a * a := Nat.add_le_add (Nat.mul_le_mul_left _ h1) h2
    _ = (k + 1) * (a * a) := by ring
    _ ≤ a * (a * a) := Nat.mul_le_mul_right _ hk
    _ = a ^ 3 := by ring
end PaddedDescent.F.Arith
