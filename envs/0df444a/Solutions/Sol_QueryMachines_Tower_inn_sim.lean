-- Prove2me | solution 1 for QueryMachines.Tower.inn_sim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:27.326285+00:00
-- url     : https://prove2.me/submissions/fcf7acf2-b0ed-4d4d-8820-d4cf8825bc2d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Chain
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_Runs
import Definitions.Def_Tower_TowerRuns
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
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
import Theorems.Thm_QueryMachines_Tower_chain_facts
import Theorems.Thm_QueryMachines_Tower_up_ok
import Theorems.Thm_QueryMachines_Tower_wfHalt
import Theorems.Thm_QueryMachines_Tower_wfMono
import Theorems.Thm_QueryMachines_Tower_wfQuery
import Theorems.Thm_QueryMachines_Tower_wfStep
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum
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
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Ctx Q G A : Type} [HasSize Ctx] {P : Spec Ctx Q A} {gl : G → Option A} {wg : G → ℕ} {Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A} {Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A}
  {TS : ℕ → ℕ → ℕ → ℕ} {TI : ℕ → ℕ → ℕ} {SS SI SC : ℕ} {c0 : Ctx} {f0 : Q → Option A} {tq : ℕ}
namespace QueryMachines.Tower
theorem _root_.solution (hM : P.Meets gl wg Sol Inn TS TI SS SI SC) (hG : P.Good c0 f0) (env : List Ctx) (hC : Chain P c0 f0 env) (c : Ctx) (q : Q) {b : A} {i : Inn.σ} {own : ℕ} {L : List (Q ⊕ G)}
    (hr : Inn.Reaches (Sum.elim (tabs P f0 env) gl) SI b i own L) :
    (nest Sol Inn).WithinFrom (callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P) (Sum.inr (c, env, q))) (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2) (Sum.inr (env, i) : NSt Sol Inn) (own + (L.map (Sum.elim (fun _ => price P TI tq env) wg)).sum) (P.lev c0 * (SC + 1) + SS + SI + 2) b := by
  obtain ⟨hGd, hlev, hsize⟩ := chain_facts hM hG env hC
  have hsz : ∀ i : Inn.σ, size i ≤ SI → size (Sum.inr (env, i) : NSt Sol Inn) ≤ (P.lev c0 * (SC + 1) + SS + SI + 2) := fun i hi => by
    have : env.length * (SC + 1) ≤ P.lev c0 * (SC + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [size_inr, size_prod]; dsimp only; omega
  induction hr with
  | halt h1 h2 => exact wfHalt (M := nest Sol Inn) h1 (hsz _ h2)
  | @step i own L h1 h2 h3 _ ih =>
    have ha : (nest Sol Inn).ask (Sum.inr (env, i) : NSt Sol Inn) = none := by simp [nest, h2]
    exact wfMono (wfStep (M := nest Sol Inn) (s := (Sum.inr (env, i) : NSt Sol Inn)) h1 ha (hsz _ h3) ih) (by omega) le_rfl
  | @query i own L y v h1 h2 h3 h4 _ ih =>
    obtain ⟨r, ho, rfl, hw⟩ := up_ok tq gl wg TS env hC y v h3 (Sum.inr (c, env, q)) (le_refl env.length)
    have ha : (nest Sol Inn).ask (Sum.inr (env, i) : NSt Sol Inn) = some (upQuery env y) := by simp [nest, h2]
    refine wfMono (wfQuery (M := nest Sol Inn) (s := (Sum.inr (env, i) : NSt Sol Inn)) (w := (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2)) h1 ha ho (hsz _ h4) ih) ?_ le_rfl
    rw [hw]; simp only [List.map_cons, List.sum_cons]; omega
end QueryMachines.Tower
