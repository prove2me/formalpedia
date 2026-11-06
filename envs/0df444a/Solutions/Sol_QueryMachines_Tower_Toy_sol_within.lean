-- Prove2me | solution 1 for QueryMachines.Tower.Toy.sol_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:18:46.75451+00:00
-- url     : https://prove2.me/submissions/c912a7c7-5bc6-41c2-80b9-5aaaf7c14ee1

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
import Theorems.Thm_QueryMachines_Tower_Toy_size_start
import Theorems.Thm_QueryMachines_Tower_Toy_size_one
import Theorems.Thm_QueryMachines_Tower_Toy_size_two
import Theorems.Thm_QueryMachines_Tower_Toy_size_done
import Theorems.Thm_QueryMachines_Tower_Toy_oracle_call
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_QueryMachines_Tower_Toy_sumF_le
import Theorems.Thm_QueryMachines_Tower_wfHalt
import Theorems.Thm_QueryMachines_Tower_wfMono
import Theorems.Thm_QueryMachines_Tower_wfQuery
import Theorems.Thm_QueryMachines_Tower_wfStep
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
theorem _root_.solution (ℓ0 M0 : ℕ) (c : ℕ × Bool) (f : List Bool → Option ℕ) (hG : (spec ℓ0 M0).Good c f) (tc tq : ℕ) :
    Sol.Within ((spec ℓ0 M0).oracle noG c f) (Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) noW)) c (TS c.1 tc tq) (SS ℓ0 M0) (sumF c.1 f) := by
  obtain ⟨l, b⟩ := c
  obtain ⟨hl, hf⟩ := hG
  replace hl : l ≤ ℓ0 := hl
  replace hf : ∀ q : List Bool, q.length = l → ∃ a, a ≤ M0 ∧ f q = some a := hf
  have hls := Nat.size_le_size hl
  have hV : sumF l f ≤ 2 ^ ℓ0 * M0 := (sumF_le M0 l f hf).trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hl))
  have hVs := Nat.size_le_size hV
  show Sol.WithinFrom _ _ ((l, Sum.inl ()) : ℕ × Ph) (TS l tc tq) (SS ℓ0 M0) (sumF l f)
  cases l with
  | zero =>
    obtain ⟨a, ha, e⟩ := hf [] rfl
    have hval : sumF 0 f = a := by simp [sumF, e]
    rw [hval] at hVs ⊢
    have h2 : Sol.WithinFrom ((spec ℓ0 M0).oracle noG (0, b) f) (Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) noW)) ((0, Sum.inr (Sum.inr (Sum.inr a))) : ℕ × Ph) 0 (SS ℓ0 M0) a :=
      wfHalt rfl (by show size ((0, Sum.inr (Sum.inr (Sum.inr a))) : ℕ × Ph) ≤ _; rw [size_done, SS]; omega)
    have h1 := wfQuery (M := Sol) (s := ((0, Sum.inl ()) : ℕ × Ph)) (x := Sum.inr (Sum.inl [])) (v := a) rfl rfl e
      (by show size ((0, Sum.inl ()) : ℕ × Ph) ≤ _; rw [size_start, SS]; omega) h2
    exact wfMono h1 (by show 0 + tq ≤ tq; omega) le_rfl
  | succ l =>
    have hu : sumF l (fun q => f (false :: q)) ≤ sumF (l + 1) f := Nat.le_add_right _ _
    have hv : sumF l (fun q => f (true :: q)) ≤ sumF (l + 1) f := Nat.le_add_left _ _
    have hus := Nat.size_le_size hu
    have hvs := Nat.size_le_size hv
    generalize hU : sumF l (fun q => f (false :: q)) = u at *
    generalize hW : sumF l (fun q => f (true :: q)) = v at *
    have hsum : sumF (l + 1) f = u + v := by simp only [sumF, hU, hW]
    rw [hsum] at hVs hus hvs ⊢
    have h5 : Sol.WithinFrom ((spec ℓ0 M0).oracle noG (l + 1, b) f) (Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) noW)) ((l + 1, Sum.inr (Sum.inr (Sum.inr (u + v)))) : ℕ × Ph) 0 (SS ℓ0 M0) (u + v) :=
      wfHalt rfl (by show size ((l + 1, Sum.inr (Sum.inr (Sum.inr (u + v)))) : ℕ × Ph) ≤ _; rw [size_done, SS]; omega)
    have h4 := wfStep (M := Sol) (s := ((l + 1, Sum.inr (Sum.inr (Sum.inl (u, v)))) : ℕ × Ph)) rfl rfl
      (by show size ((l + 1, Sum.inr (Sum.inr (Sum.inl (u, v)))) : ℕ × Ph) ≤ _; rw [size_two, SS]; omega) h5
    have h3 := wfQuery (M := Sol) (s := ((l + 1, Sum.inr (Sum.inl u)) : ℕ × Ph)) (x := Sum.inl (l, true)) (v := v) rfl rfl (by rw [oracle_call, hW])
      (by show size ((l + 1, Sum.inr (Sum.inl u)) : ℕ × Ph) ≤ _; rw [size_one, SS]; omega) h4
    have h2 := wfQuery (M := Sol) (O := (spec ℓ0 M0).oracle noG (l + 1, b) f) (w := Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) noW)) (S := SS ℓ0 M0) (s := ((l + 1, Sum.inl ()) : ℕ × Ph))
      (x := Sum.inl (l, false)) (v := u) rfl (by simp [Sol, solAsk]) (by rw [oracle_call, hU])
      (by show size ((l + 1, Sum.inl ()) : ℕ × Ph) ≤ _; rw [size_start, SS]; omega)
      (by rw [show Sol.resume ((l + 1, Sum.inl ()) : ℕ × Ph) u = ((l + 1, Sum.inr (Sum.inl u)) : ℕ × Ph) by simp [Sol, solResume]]; exact h3)
    exact wfMono h2 (by show 0 + 1 + tc + tc ≤ 2 * tc + 1; omega) le_rfl
end QueryMachines.Tower.Toy
