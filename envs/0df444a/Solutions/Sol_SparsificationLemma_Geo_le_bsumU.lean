-- Prove2me | solution 1 for SparsificationLemma.Geo.le_bsumU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:55:49.470297+00:00
-- url     : https://prove2.me/submissions/489dd077-7d76-4182-905a-e7302d5ab8d4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_SparsificationLemma_Geo_Thr
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsificationLemma_Geo_Tau

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Geo
open Finset Groundwork Groundwork.Sparsify CountKSat UniformInK
namespace SparsificationLemma.Geo
theorem _root_.solution {k τ : ℕ} (hτ : 2 ≤ τ) : k ≤ bsumU τ k := by
  unfold bsumU
  calc k ≤ 2 * k := by omega
    _ ≤ 2 ^ (2 * k) := Nat.lt_two_pow_self.le
    _ ≤ τ ^ (2 * k) := Nat.pow_le_pow_left hτ _
end SparsificationLemma.Geo
