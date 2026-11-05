-- Prove2me | solution 1 for SparsificationLemma.Cal.catalan_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:15:42.178538+00:00
-- url     : https://prove2.me/submissions/f82275ee-1352-4945-a436-3c8a0e8b4dd0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Beta

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset
namespace SparsificationLemma.Cal
theorem _root_.solution (j : ℕ) : 0 < catalan j := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have e := succ_mul_catalan_eq_centralBinom j
  rw [h, Nat.mul_zero] at e
  exact (Nat.centralBinom_pos j).ne e
end SparsificationLemma.Cal
