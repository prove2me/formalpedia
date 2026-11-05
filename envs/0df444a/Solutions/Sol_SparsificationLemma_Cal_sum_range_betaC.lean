-- Prove2me | solution 1 for SparsificationLemma.Cal.sum_range_betaC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:35:27.336803+00:00
-- url     : https://prove2.me/submissions/fdf5393f-feaf-4dc2-b006-dcc208058a38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Beta
import Theorems.Thm_SparsificationLemma_Cal_betaC_zero

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset
namespace SparsificationLemma.Cal
theorem _root_.solution (α : ℕ) {k : ℕ} (hk : 1 ≤ k) : ∑ c ∈ range k, betaC α c = ∑ c ∈ Ico 1 k, betaC α c := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), betaC_zero, Nat.zero_add]
end SparsificationLemma.Cal
