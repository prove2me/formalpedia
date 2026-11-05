-- Prove2me | solution 1 for SparsificationLemma.Cal.stDegSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:36:53.010809+00:00
-- url     : https://prove2.me/submissions/82ddc433-252d-4d74-94ca-1f12add42305

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Beta
import Theorems.Thm_SparsificationLemma_Cal_thetaC_of_pos
import Theorems.Thm_SparsificationLemma_Cal_factIV

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset
namespace SparsificationLemma.Cal
theorem _root_.solution : StDegSum := by
  intro α k hα hk
  have h1 : ∑ j ∈ range k, thetaC α j = 2 + α * ∑ c ∈ Ico 1 k, betaC α c := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), mul_sum]
    exact congrArg (2 + ·) (sum_congr rfl fun c hc => thetaC_of_pos α (mem_Ico.1 hc).1)
  refine ⟨h1, ?_, ?_⟩
  · rw [h1, Nat.mul_assoc 4, Nat.mul_left_comm 4]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (factIV α k hα hk)) _
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega, pow_succ]
    ring
end SparsificationLemma.Cal
