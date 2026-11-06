-- Prove2me | solution 1 for SplitSat.size_stack_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:55:14.697345+00:00
-- url     : https://prove2.me/submissions/55c92a51-3a79-4ebf-8d16-eed450bc7fdb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
import Theorems.Thm_SplitSat_size_list_le
import Theorems.Thm_SplitSat_size_node_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_size_list_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_TM_update_withIO
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
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.TM.update_withIO
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
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify
namespace SplitSat
theorem _root_.solution {k n a Dd : ℕ} {st : List Fml} (hl : st.length ≤ Dd * n + 1)
    (hst : ∀ x ∈ st, x.length ≤ a * (n + 2) ^ k ∧ ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    size (st.map fun y => ((List.replicate n (), y) : NFml)) ≤ ((Dd + 1) * (a * (2 * k + 1) + 4) + 1) * (n + 2) ^ (k + 2) := by
  have h1 := size_list_le (l := st.map fun y => ((List.replicate n (), y) : NFml)) (k := Dd * n + 1)
    (s := (a * (2 * k + 1) + 3) * (n + 2) ^ (k + 1)) (by simpa using hl) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact size_node_le (hst x hx).1 (hst x hx).2)
  refine h1.trans ?_
  have e1 : 1 ≤ (n + 2) ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  have e2 : 1 ≤ (n + 2) ^ (k + 2) := Nat.one_le_pow _ _ (by omega)
  have hp : Dd * n + 1 ≤ (Dd + 1) * (n + 2) := by
    have a1 : Dd * n ≤ Dd * (n + 2) := Nat.mul_le_mul_left _ (by omega)
    have a3 : (Dd + 1) * (n + 2) = Dd * (n + 2) + (n + 2) := by ring
    omega
  have hp2 : (a * (2 * k + 1) + 3) * (n + 2) ^ (k + 1) + 1 ≤ (a * (2 * k + 1) + 4) * (n + 2) ^ (k + 1) := by
    have a3 : (a * (2 * k + 1) + 4) * (n + 2) ^ (k + 1) = (a * (2 * k + 1) + 3) * (n + 2) ^ (k + 1) + (n + 2) ^ (k + 1) := by ring
    omega
  calc (Dd * n + 1) * ((a * (2 * k + 1) + 3) * (n + 2) ^ (k + 1) + 1) + 1
      ≤ (Dd + 1) * (n + 2) * ((a * (2 * k + 1) + 4) * (n + 2) ^ (k + 1)) + 1 := Nat.succ_le_succ (Nat.mul_le_mul hp hp2)
    _ = (Dd + 1) * (a * (2 * k + 1) + 4) * (n + 2) ^ (k + 2) + 1 := by ring
    _ ≤ (Dd + 1) * (a * (2 * k + 1) + 4) * (n + 2) ^ (k + 2) + (n + 2) ^ (k + 2) := Nat.add_le_add_left e2 _
    _ = ((Dd + 1) * (a * (2 * k + 1) + 4) + 1) * (n + 2) ^ (k + 2) := by ring
end SplitSat
