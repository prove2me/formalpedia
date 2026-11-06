-- Prove2me | solution 1 for PairsToBound.foldr_max_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:52:34.477118+00:00
-- url     : https://prove2.me/submissions/fee24782-9ba9-4e6a-be33-b00ea77d277b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_SparsificationLemma_StepSparsify
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Width

set_option autoImplicit false
section
section
open PairsToBound
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution {l : List ℕ} {a b : ℕ} (ha : a ≤ b) (h : ∀ x ∈ l, x ≤ b) : l.foldr max a ≤ b := by
  induction l with
  | nil => exact ha
  | cons c l ih =>
    rw [List.foldr_cons]
    exact max_le (h c List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
end PairsToBound
