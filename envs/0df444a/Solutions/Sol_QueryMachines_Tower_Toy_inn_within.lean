-- Prove2me | solution 1 for QueryMachines.Tower.Toy.inn_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:01:00.113977+00:00
-- url     : https://prove2.me/submissions/184afacf-c3d0-4d55-acfb-42380969ba6d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Toy_Defs
import Definitions.Def_Tower_Toy_Spec
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_TowerRuns
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Tactic.Ring
import Definitions.Def_Tower_Toy_Meets
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_size_bools
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
import Theorems.Thm_QueryMachines_QueryMachine_close_subst
import Theorems.Thm_QueryMachines_Tower_wfHalt
import Theorems.Thm_QueryMachines_Tower_wfMono
import Theorems.Thm_QueryMachines_Tower_wfQuery
attribute [local fun_prop] Groundwork.PolyT.length
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
open QueryMachines QueryMachines.Tower QueryMachines.Tower.Toy
open Groundwork Groundwork.Prog
namespace QueryMachines.Tower.Toy
theorem _root_.solution (ℓ0 M0 : ℕ) (c : ℕ × Bool) (f : List Bool → Option ℕ) (c' : ℕ × Bool) (hG : (spec ℓ0 M0).Good c f) (hch : (spec ℓ0 M0).Child c f c') (q : List Bool) (a : ℕ)
    (ht : (spec ℓ0 M0).tab c' f q = some a) (tq : ℕ) : Inn.Within (Sum.elim f noG) (Sum.elim (fun _ => tq) noW) (c', q) (TI c'.1 tq) (SI ℓ0 M0) a := by
  replace hch : c'.1 + 1 = c.1 := hch
  replace ht : (if q.length = c'.1 then f (c'.2 :: q) else none) = some a := ht
  have hl : c.1 ≤ ℓ0 := hG.1
  by_cases hq : q.length = c'.1
  · rw [if_pos hq] at ht
    obtain ⟨a', ha', e⟩ := hG.2 (c'.2 :: q) (by rw [List.length_cons, hq]; exact hch)
    obtain rfl : a' = a := Option.some.inj (e.symm.trans ht)
    have has := Nat.size_le_size ha'
    have h2 : Inn.WithinFrom (Sum.elim f noG) (Sum.elim (fun _ => tq) noW) (Sum.inr a' : (Bool × List Bool) ⊕ ℕ) 0 (SI ℓ0 M0) a' :=
      wfHalt rfl (by show size (Sum.inr a' : (Bool × List Bool) ⊕ ℕ) ≤ _; rw [size_inr, size_nat, SI]; omega)
    have h1 := wfQuery (M := Inn) (s := (Sum.inl (c'.2, q) : (Bool × List Bool) ⊕ ℕ)) (x := Sum.inl (c'.2 :: q)) (v := a') rfl rfl ht
      (by show size (Sum.inl (c'.2, q) : (Bool × List Bool) ⊕ ℕ) ≤ _; rw [size_inl, size_prod, size_bool, size_bools, SI]; dsimp only; omega) h2
    exact wfMono h1 (by show 0 + tq ≤ tq; omega) le_rfl
  · rw [if_neg hq] at ht; cases ht
end QueryMachines.Tower.Toy
