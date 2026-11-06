-- Prove2me | solution 1 for SizeCircuit.len_iterate_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:00:15.319307+00:00
-- url     : https://prove2.me/submissions/fb827ca7-65d4-4eeb-ba02-d6c37a988272

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_SizeCircuit_Addition
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_List3
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Cert
import Theorems.Thm_SizeCircuit_len_list_le
import Theorems.Thm_SizeCircuit_len_nat_le
import Theorems.Thm_SizeCircuit_len_gate_le
import Theorems.Thm_SizeCircuit_lt_of_wfa
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
import Theorems.Thm_SizeCircuit_iterate_spec
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
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution (n k m : ℕ) (hk : k ≤ n) (hm : n ≤ m) : len ((addStep n)^[k] (addStart n)) ≤ stateLen m := by
  obtain ⟨⟨g1, g2, g3, g4, -⟩, h1, h2, h3⟩ := iterate_spec n k hk
  generalize (addStep n)^[k] (addStart n) = st at g1 g2 g3 g4 h1 h2 h3 ⊢
  obtain ⟨cur, nxt, dig, K⟩ := st
  dsimp only at g1 g2 g3 g4 h1 h2 h3
  have e1 : len cur ≤ m * (3 * (6 * m) + 2 + 2) + 2 := len_list_le (fun x hx => len_nat_le (by have := g1 x hx; omega)) (by omega)
  have e2 : len nxt ≤ m * (3 * (6 * m) + 2 + 2) + 2 := len_list_le (fun x hx => len_nat_le (by have := g2 x hx; omega)) (by omega)
  have e3 : len dig ≤ m * (3 * (6 * m) + 2 + 2) + 2 := len_list_le (fun x hx => len_nat_le (by have := g3 x hx; omega)) (by omega)
  have e4 : len K ≤ 5 * m * (6 * (6 * m) + 18 + 2) + 2 :=
    len_list_le (fun g hg => len_gate_le g (by have := lt_of_wfa g4 g hg; omega) (by have := lt_of_wfa g4 g hg; omega)) (by omega)
  simp only [len_pair, stateLen]
  omega
end SizeCircuit
