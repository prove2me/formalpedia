-- Prove2me | solution 1 for Sat3.log2_log2_le_sOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:33:09.32691+00:00
-- url     : https://prove2.me/submissions/a4178158-f838-4c3f-9bab-752d4153189d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
import Definitions.Def_PaddedDescent_RateLemmas

set_option autoImplicit false
section
section
open Sat3
open Turing
open scoped NNReal ENNReal
namespace Sat3
theorem _root_.solution (n : ℕ) : 3 * (Nat.log2 (Nat.log2 n) + 2) ≤ 19 * (PaddedDescent.sOf n + 146) := by
  unfold PaddedDescent.sOf
  omega
end Sat3
