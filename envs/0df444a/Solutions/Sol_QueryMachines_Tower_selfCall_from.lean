-- Prove2me | solution 1 for QueryMachines.Tower.selfCall_from
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:39:00.780793+00:00
-- url     : https://prove2.me/submissions/b998976c-eb71-454f-9f3e-673ea2387b8a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_Runs
import Theorems.Thm_QueryMachines_Tower_rout_none
import Theorems.Thm_QueryMachines_Tower_rask_halted
import Theorems.Thm_QueryMachines_Tower_rask_none
import Theorems.Thm_QueryMachines_Tower_rask_call
import Theorems.Thm_QueryMachines_Tower_rask_query
import Theorems.Thm_QueryMachines_Tower_rstep_step
import Theorems.Thm_QueryMachines_Tower_rstep_call
import Theorems.Thm_QueryMachines_Tower_rstep_pop
import Theorems.Thm_QueryMachines_Tower_size_stack
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_elim
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
import Theorems.Thm_QueryMachines_Tower_wfMono
import Theorems.Thm_QueryMachines_Tower_wfQuery
import Theorems.Thm_QueryMachines_Tower_wfStep
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
variable {Q A α β : Type} (M : QueryMachine (Q ⊕ α) (A ⊕ β) α β)
namespace QueryMachines.Tower
theorem _root_.solution (O : Q → Option A) (w : Q → ℕ) (Good : α → Prop) (val : α → β) (dep T : α → ℕ) (S : ℕ)
    (H : ∀ a, Good a → M.Within (callOracle O Good val dep a) (Sum.elim w fun a' => T a' + 2) a (T a) S (val a)) :
    ∀ (n : ℕ) (a : α), dep a = n → Good a → ∀ (s : M.σ) (own : ℕ) (L : List (Q ⊕ α)), M.Reaches (callOracle O Good val dep a) S (val a) s own L →
    ∀ (K : List M.σ) (S' tk : ℕ) (b : β), size K + (dep a + 1) * (S + 1) ≤ S' →
      (∀ sh : M.σ, M.out sh = some (val a) → size sh ≤ S → (selfCall M).WithinFrom O w (sh :: K : List M.σ) tk S' b) →
      (selfCall M).WithinFrom O w (s :: K : List M.σ) (own + (L.map (Sum.elim w fun a' => T a' + 2)).sum + tk) S' b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro a hn hG s own L hr K S' tk b hS hc
  have hmul : (dep a + 1) * (S + 1) = dep a * (S + 1) + (S + 1) := Nat.succ_mul _ _
  have hsz : ∀ s : M.σ, size s ≤ S → size (s :: K : List M.σ) ≤ S' := fun s hs => by rw [size_stack]; omega
  induction hr with
  | halt h1 h2 => exact wfMono (hc _ h1 h2) (by omega) le_rfl
  | @step s own L h1 h2 h3 _ ih =>
    have h := wfStep (M := selfCall M) (s := (s :: K : List M.σ)) (O := O) (w := w) (rout_none M K h1) (rask_none M K h1 h2) (hsz _ h3)
      (by rw [show (selfCall M).step (s :: K : List M.σ) = (M.step s :: K : List M.σ) from rstep_step M K h1 h2]; exact ih)
    exact wfMono h (by omega) le_rfl
  | @query s own L x v h1 h2 h3 h4 _ ih =>
    rcases x with q | a'
    · obtain ⟨v0, hv0, rfl⟩ : ∃ v0, O q = some v0 ∧ Sum.inl v0 = v := by simpa [callOracle] using h3
      have h := wfQuery (M := selfCall M) (s := (s :: K : List M.σ)) (O := O) (w := w) (rout_none M K h1) (rask_query M K h1 h2) hv0 (hsz _ h4) ih
      refine wfMono h ?_ le_rfl
      simp only [List.map_cons, List.sum_cons, Sum.elim_inl]; omega
    · obtain ⟨⟨hG', hd⟩, rfl⟩ : (Good a' ∧ dep a' < dep a) ∧ Sum.inr (val a') = v := by
        simpa [callOracle] using h3
      obtain ⟨own', L', hr', hc'⟩ := H a' hG'
      have hle : (dep a' + 1) * (S + 1) ≤ dep a * (S + 1) := Nat.mul_le_mul_right _ hd
      have hsz2 : ∀ sh : M.σ, size sh ≤ S → size (sh :: s :: K : List M.σ) ≤ S' := fun sh hs => by
        have : S + 1 ≤ (dep a' + 1) * (S + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
        rw [size_stack, size_stack]; omega
      have hcall := IH (dep a') (hn ▸ hd) a' rfl hG' _ own' L' hr' (s :: K) S' (own + (L.map (Sum.elim w fun a' => T a' + 2)).sum + tk + 1) b
        (by rw [size_stack]; omega)
        (fun sh g1 g2 => wfStep (M := selfCall M) (s := (sh :: s :: K : List M.σ)) rfl (rask_halted M (s :: K) g1) (hsz2 _ g2)
          (by rw [show (selfCall M).step (sh :: s :: K : List M.σ) = (M.resume s (Sum.inr (val a')) :: K : List M.σ) from rstep_pop M K g1]; exact ih))
      have h := wfStep (M := selfCall M) (s := (s :: K : List M.σ)) (O := O) (w := w) (rout_none M K h1) (rask_call M K h1 h2) (hsz _ h4)
        (by rw [show (selfCall M).step (s :: K : List M.σ) = (M.init a' :: s :: K : List M.σ) from rstep_call M K h1 h2]; exact hcall)
      refine wfMono h ?_ le_rfl
      simp only [List.map_cons, List.sum_cons, Sum.elim_inr]; omega
end QueryMachines.Tower
