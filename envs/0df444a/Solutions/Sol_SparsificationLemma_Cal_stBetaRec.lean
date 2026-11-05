-- Prove2me | solution 1 for SparsificationLemma.Cal.stBetaRec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:15:16.550588+00:00
-- url     : https://prove2.me/submissions/4e932d75-567c-4f91-a464-70023ff5b1bc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Beta
import Theorems.Thm_SparsificationLemma_Cal_betaC_add_two

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset
namespace SparsificationLemma.Cal
theorem _root_.solution : StBetaRec := by
  intro α c hc
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hc
  rw [betaC_add_two, sum_Ico_eq_sum_range, Fin.sum_univ_eq_sum_range (fun h => 4 * α * betaC α (c + 1 - h) * betaC α (h + 1)) (c + 1)]
  refine sum_congr rfl fun h _ => ?_
  rw [show c + 2 - (1 + h) = c + 1 - h by omega, Nat.add_comm 1 h]
end SparsificationLemma.Cal
