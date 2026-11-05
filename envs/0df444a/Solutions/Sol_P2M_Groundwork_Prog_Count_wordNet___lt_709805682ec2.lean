-- Prove2me | solution 1 for P2M_Groundwork_Prog_Count_wordNet___lt_709805682ec2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:22:30.555199+00:00
-- url     : https://prove2.me/submissions/6cde4a01-5774-43a2-83f8-12340995c988

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Theorems.Thm_Groundwork_Prog_Count_sum_words_zip
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}
namespace Groundwork.Prog.Count
theorem _root_.solution {a b : Fin g} (h : a < b) (z z' : List Bool) : (wordNet g k φ).Ψ a b z z' =
    if ((links g k φ a.val b.val).all fun p => z.getD p.1 false == z'.getD p.2 false) then 1 else 0 := by
  have h' : a.val < b.val := h
  have hn : ¬ b.val < a.val := by omega
  simp only [Network.Ψ, Network.lab, wordNet, fF, min_eq_left h.le, max_eq_right h.le, capF, min_eq_left h'.le,
    max_eq_right h'.le, if_pos h', if_neg hn]
  exact sum_words_zip (links g k φ a.val b.val) (fun p => z.getD p.1 false) (fun p => z'.getD p.2 false)
end Groundwork.Prog.Count
