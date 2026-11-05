-- Prove2me | solution 1 for SparsificationLemma.Cal.betaC_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:22:38.261503+00:00
-- url     : https://prove2.me/submissions/7d8db447-9d93-4d9a-a415-34c33b0bf060

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Beta
import Theorems.Thm_SparsificationLemma_Cal_stBetaCat
import Theorems.Thm_SparsificationLemma_Cal_catalan_pos

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset
namespace SparsificationLemma.Cal
theorem _root_.solution {α : ℕ} (hα : 1 ≤ α) (c : ℕ) : 0 < betaC α (c + 1) := by
  rw [stBetaCat]
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.pow_pos (by omega))) (catalan_pos c)
end SparsificationLemma.Cal
