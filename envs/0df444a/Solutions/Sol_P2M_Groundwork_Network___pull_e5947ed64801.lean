-- Prove2me | solution 1 for P2M_Groundwork_Network___pull_e5947ed64801
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:07:13.786505+00:00
-- url     : https://prove2.me/submissions/fd2b8489-0919-433f-ac99-872f8b5ae886

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Definitions.Def_StepMachines_Math_Pull
import Theorems.Thm_Groundwork_Code_sum_words
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Network
variable {J σ τ : Type*}
variable [Fintype J] [LinearOrder J] (N : Network J σ τ) (n : J → ℕ) (cs : ∀ a, Code (N.S a) (n a))
  (cl : ∀ a b, Code (N.Θ a b) (N.c a b))
omit [Fintype J]
namespace Groundwork.Network
theorem _root_.solution (a b : J) (z z' : List Bool) :
    (N.pull n cs cl).Ψ a b z z' = N.Ψ a b ((cs a).dec z) ((cs b).dec z') := by
  unfold Ψ
  simp only [lab, pull]
  rw [min_comm b a, max_comm b a, ← (cl (min a b) (max a b)).sum_words]
  refine Finset.sum_congr rfl fun θ _ => ?_
  split_ifs <;> simp
end Groundwork.Network
