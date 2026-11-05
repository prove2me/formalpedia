-- Prove2me | solution 1 for SatFree.supOneGivesPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:41:35.155674+00:00
-- url     : https://prove2.me/submissions/56574654-c192-4e0d-9608-015d0d139e6a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Mathlib.Tactic
import Definitions.Def_FreeCode_Order

set_option autoImplicit false
section
section
open SatFree
open scoped NNReal ENNReal
namespace SatFree
theorem _root_.solution : SupOneGivesPositive := fun u h => by
  by_contra hc
  have h0 : (⨆ (k : ℕ) (_ : 3 ≤ k), u k) = 0 := by
    simp only [ENNReal.iSup_eq_zero]
    exact fun k hk => nonpos_iff_eq_zero.1 (not_lt.1 fun h' => hc ⟨k, hk, h'⟩)
  rw [h0] at h
  exact zero_ne_one h
end SatFree
