-- Prove2me | solution 1 for Variance.sum_ordered_c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:14:47.041437+00:00
-- url     : https://prove2.me/submissions/b6ebc6c9-80fe-4548-9feb-c4025a04de50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Cov
import Theorems.Thm_Variance_sum_ordered

set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks
namespace Variance
theorem _root_.solution {g : ℕ} (c : Fin g → Fin g → ℕ) : ∑ p ∈ ordered g, c p.1 p.2 = ∑ a, ∑ b ∈ univ.erase a, c a b := sum_ordered fun p => c p.1 p.2
end Variance
