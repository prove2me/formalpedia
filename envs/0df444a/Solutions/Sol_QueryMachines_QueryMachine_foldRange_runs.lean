-- Prove2me | solution 1 for QueryMachines.QueryMachine.foldRange_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:14:40.38801+00:00
-- url     : https://prove2.me/submissions/f73e41f6-e2be-47c9-bacf-8fea6eb852c9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_QueryMachines_QueryMachine_foldWhile_reaches
import Theorems.Thm_QueryMachines_QueryMachine_orbit_range
import Theorems.Thm_QueryMachines_QueryMachine_sum_map_range
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_Stepped_foldWhile_reaches
import Theorems.Thm_Groundwork_Stepped_orbit_range
import Theorems.Thm_Groundwork_Stepped_sum_map_range
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
import Theorems.Thm_QueryMachines_QueryMachine_close_subst
attribute [local fun_prop] Groundwork.PolyT.flatMap
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
attribute [local simp] QueryMachines.QueryMachine.close_subst



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}
namespace QueryMachines.QueryMachine
theorem _root_.solution [HasSize α] [HasSize γ] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) β} {g : γ → ℕ → β → γ} {c₀ : α → γ} {O : Q → Option A} {a : α}
    (t : ℕ → ℕ) (Lq : ℕ → List Q) (v : ℕ → β) (Sc Sm : ℕ) (hM : ∀ y < N a, M.Runs O (a, y) (t y) (Lq y) Sm (v y))
    (hc : ∀ k ≤ N a, size ((List.range k).foldl (fun c y => g c y (v y)) (c₀ a)) ≤ Sc) :
    (foldRange N M g c₀).Runs O a (∑ y ∈ range (N a), (t y + 1)) ((List.range (N a)).flatMap Lq) (size a + size (N a) + (Sc + Sm) + 1)
      ((List.range (N a)).foldl (fun c y => g c y (v y)) (c₀ a)) := by
  have ho := orbit_range N a (N a) 0 (by omega)
  rw [← List.range_eq_range'] at ho
  have := foldWhile_reaches (start := Stepped.rangeStart N) (M := M) (g := Stepped.rangeG g) (c₀ := c₀) (O := O) ho (fun x => t x.2) (fun x => Lq x.2) (fun x => v x.2)
    (size a + size (N a)) Sc Sm (c₀ a)
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hM y (List.mem_range.1 hy))
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have := Nat.size_le_size (List.mem_range.1 hy).le
      simp only [size_prod, size_nat]; omega)
    (by
      intro l hl
      rw [List.prefix_iff_eq_take] at hl
      rw [hl, ← List.map_take, List.take_range, List.foldl_map]
      exact hc _ (min_le_right _ _))
  rw [List.map_map, List.foldl_map, List.flatMap_map] at this
  rw [← sum_map_range]
  exact this
end QueryMachines.QueryMachine
