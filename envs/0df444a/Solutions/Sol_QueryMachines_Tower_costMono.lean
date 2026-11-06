-- Prove2me | solution 1 for QueryMachines.Tower.costMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:18:28.856343+00:00
-- url     : https://prove2.me/submissions/2206b94d-5b6d-4459-a11d-f6c5c8197450

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Mathlib.Tactic.Ring
import Definitions.Def_Tower_Cost

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
namespace QueryMachines.Tower
theorem _root_.solution {TS : ℕ → ℕ → ℕ → ℕ} {TI : ℕ → ℕ → ℕ} (hS : ∀ l tc tc' tq tq', tc ≤ tc' → tq ≤ tq' → TS l tc tq ≤ TS l tc' tq') (hI : ∀ l t t', t ≤ t' → TI l t ≤ TI l t') :
    ∀ l t t', t ≤ t' → cost TS TI l t ≤ cost TS TI l t'
  | 0, _, _, h => hS 0 _ _ _ _ le_rfl h
  | l + 1, _, _, h => hS _ _ _ _ _ (Nat.add_le_add_right (solution hS hI l _ _ (Nat.add_le_add_right (hI l _ _ h) 2)) 2) h
end QueryMachines.Tower
