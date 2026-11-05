-- Prove2me | solution 1 for SparsificationLemma.Cal.stThrCal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:29:47.879141+00:00
-- url     : https://prove2.me/submissions/045468ce-4236-46bb-b5b7-0ce4b234d59c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_SparsificationLemma_Cal_Beta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Thr
import Theorems.Thm_SparsificationLemma_Cal_betaC_one
import Theorems.Thm_SparsificationLemma_Cal_betaC_pos
import Theorems.Thm_SparsificationLemma_Cal_betaC_zero
import Theorems.Thm_SparsificationLemma_Cal_stBetaRec
import Theorems.Thm_SparsificationLemma_Cal_thetaC_of_pos


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset
namespace SparsificationLemma.Cal
theorem _root_.solution : StThrCal := by
  intro α k hα
  refine ⟨fun i => ?_, (betaC_one α).ge, fun i hi _ => ?_, fun r => ?_⟩
  · rcases i with _ | i
    · exact Nat.succ_pos 1
    · exact Nat.mul_pos hα (betaC_pos hα i)
  · have hS : ∑ i' ∈ range i, 2 * thetaC α (i - i') * betaC α i' = ∑ h ∈ Ico 1 i, 2 * α * betaC α (i - h) * betaC α h := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), betaC_zero, Nat.mul_zero, Nat.zero_add]
      refine sum_congr rfl fun h hh => ?_
      obtain ⟨h1, h2⟩ := mem_Ico.1 hh
      rw [thetaC_of_pos α (by omega : 1 ≤ i - h), Nat.mul_assoc 2 α]
    have h1 : 4 * thetaC α (i - 1) ≤ ∑ h ∈ Ico 1 i, 2 * α * betaC α (i - h) * betaC α h := by
      have e : 4 * thetaC α (i - 1) = 2 * α * betaC α (i - 1) * betaC α 1 := by
        rw [thetaC_of_pos α (by omega : 1 ≤ i - 1), betaC_one]; ring
      rw [e]
      exact single_le_sum (f := fun h => 2 * α * betaC α (i - h) * betaC α h) (fun _ _ => Nat.zero_le _) (mem_Ico.2 ⟨le_refl 1, by omega⟩)
    have h2 : betaC α i = 2 * ∑ h ∈ Ico 1 i, 2 * α * betaC α (i - h) * betaC α h := by
      rw [stBetaRec α i hi, mul_sum]
      exact sum_congr rfl fun h _ => by ring
    rw [hS, h2]
    omega
  · rcases r with _ | r
    · rw [betaC_zero, Nat.mul_zero]; exact Nat.zero_le _
    · exact le_refl _
end SparsificationLemma.Cal
