-- Prove2me | solution 1 for QueryMachines.Tower.sol_sim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:21.431262+00:00
-- url     : https://prove2.me/submissions/0c587951-79f6-490f-91fe-2c2aff58399f

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
import Theorems.Thm_QueryMachines_Tower_callOracle_call
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
theorem _root_.solution (hM : P.Meets gl wg Sol Inn TS TI SS SI SC) (hG : P.Good c0 f0) (env : List Ctx) (hC : Chain P c0 f0 env) {b : A} {s : Sol.σ} {own : ℕ} {L : List (Ctx ⊕ (Q ⊕ G))}
    (hr : Sol.Reaches (P.oracle gl (parent c0 env) (tabs P f0 env)) SS b s own L) :
    (nest Sol Inn).WithinFrom (callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P) (Sum.inl (env, parent c0 env))) (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2) (Sum.inl (env, s) : NSt Sol Inn)
      (own + (L.map (Sum.elim (fun _ => callCost TS TI (P.lev (parent c0 env)) (price P TI tq env)) (Sum.elim (fun _ => price P TI tq env) wg))).sum) (P.lev c0 * (SC + 1) + SS + SI + 2) b := by
  obtain ⟨hGd, hlev, hsize⟩ := chain_facts hM hG env hC
  have hsz : ∀ s : Sol.σ, size s ≤ SS → size (Sum.inl (env, s) : NSt Sol Inn) ≤ (P.lev c0 * (SC + 1) + SS + SI + 2) := fun s hs => by
    have : env.length * (SC + 1) ≤ P.lev c0 * (SC + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [size_inl, size_prod]; dsimp only; omega
  induction hr with
  | halt h1 h2 => exact wfHalt (M := nest Sol Inn) h1 (hsz _ h2)
  | @step s own L h1 h2 h3 _ ih =>
    have ha : (nest Sol Inn).ask (Sum.inl (env, s) : NSt Sol Inn) = none := by simp [nest, h2]
    exact wfMono (wfStep (M := nest Sol Inn) (s := (Sum.inl (env, s) : NSt Sol Inn)) h1 ha (hsz _ h3) ih) (by omega) le_rfl
  | @query s own L z v h1 h2 h3 h4 _ ih =>
    rcases z with c' | y
    · obtain ⟨hch, rfl⟩ : P.Child (parent c0 env) (tabs P f0 env) c' ∧ P.val c' (P.tab c' (tabs P f0 env)) = v := by simpa [Spec.oracle] using h3
      have hl := hM.child_lev _ _ c' hGd hch
      have ha : (nest Sol Inn).ask (Sum.inl (env, s) : NSt Sol Inn) = some (Sum.inr (Sum.inl (c' :: env, c'))) := by simp [nest, h2]
      have ho : callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P) (Sum.inl (env, parent c0 env)) (Sum.inr (Sum.inl (c' :: env, c'))) = some (Sum.inr (P.val c' (P.tab c' (tabs P f0 env)))) :=
        callOracle_call _ _ ⟨⟨⟨hC, hch⟩, rfl⟩, by show 2 * P.lev c' + (env.length + 1) + 1 < 2 * P.lev (parent c0 env) + env.length + 1; omega⟩
      have hw : (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2) (Sum.inr (Sum.inl (c' :: env, c'))) = callCost TS TI (P.lev (parent c0 env)) (price P TI tq env) := by rw [← hl]; rfl
      refine wfMono (wfQuery (M := nest Sol Inn) (s := (Sum.inl (env, s) : NSt Sol Inn)) (w := (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2)) h1 ha ho (hsz _ h4) ih) ?_ le_rfl
      rw [hw]; simp only [List.map_cons, List.sum_cons, Sum.elim_inl]; omega
    · obtain ⟨r, ho, rfl, hw⟩ := up_ok tq gl wg TS env hC y v (by cases y <;> exact h3) (Sum.inl (env, parent c0 env))
        (by show env.length ≤ 2 * P.lev (parent c0 env) + env.length + 1; omega)
      have ha : (nest Sol Inn).ask (Sum.inl (env, s) : NSt Sol Inn) = some (upQuery env y) := by simp [nest, h2]
      refine wfMono (wfQuery (M := nest Sol Inn) (s := (Sum.inl (env, s) : NSt Sol Inn)) (w := (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2)) h1 ha ho (hsz _ h4) ih) ?_ le_rfl
      rw [hw]; simp only [List.map_cons, List.sum_cons, Sum.elim_inr]; omega
end QueryMachines.Tower
