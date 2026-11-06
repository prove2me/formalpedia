-- Prove2me | solution 1 for VariableBound.Net.Val.st_surj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:29:57.414533+00:00
-- url     : https://prove2.me/submissions/e89d08cf-effd-4690-a358-17efa33a7ddb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_StepMachines_Math_SatNet
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Definitions.Def_VariableBound_Net_Val
import Theorems.Thm_VariableBound_Net_Val_mem_tch
import Theorems.Thm_VariableBound_Net_Val_length_st
import Theorems.Thm_VariableBound_Net_Val_getD_st_lt
import Theorems.Thm_VariableBound_Net_Val_base_iff
import Theorems.Thm_VariableBound_Net_Val_vio_iff
import Theorems.Thm_VariableBound_Net_Val_lit_lt
import Theorems.Thm_VariableBound_Net_Val_ext_of_lt
import Theorems.Thm_VariableBound_Net_Val_ext_of_le
import Theorems.Thm_VariableBound_Net_Val_mark_eq
import Theorems.Thm_VariableBound_Net_Val_ext_getD
import Theorems.Thm_VariableBound_Net_Val_getD_st_ge
import Theorems.Thm_VariableBound_Net_Val_mark_getElem
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_key
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_VariableBound_Net_Basic_div_qv_lt
import Theorems.Thm_VariableBound_Net_Basic_tchB_iff
attribute [local fun_prop] Groundwork.PolyT.filter
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



set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL ext)
variable {k g n : ℕ} {D : Dat} {y : ℕ} {fl : Bool}
namespace VariableBound.Net.Val
theorem _root_.solution (hg : 0 < g) (hw : WfD k n D) {z : Fin g → List Bool}
    (hlen : ∀ a, (z a).length = qv g n + (tch g n D a).length) (hz : Gd g n D z) :
    ∃ (σ : Fin n → Bool) (P : Finset ℕ), P ⊆ vset (ext σ) D ∧ (fun a : Fin g => st g n D (ext σ) P a) = z := by
  classical
  let σ : Fin n → Bool := fun x => (z ⟨x.1 / qv g n, div_qv_lt hg x.2⟩).getD (x.1 % qv g n) false
  let P : Finset ℕ := (Finset.range (objs D).length).filter fun e => ∃ a : Fin g, tchB g n D a e = true ∧ mark g n D a (z a) e = true
  have key : ∀ (a : Fin g) (e : ℕ), e ∈ tch g n D a → decide (e ∈ P) = mark g n D a (z a) e := by
    intro a e he
    obtain ⟨he1, he2⟩ := mem_tch.1 he
    by_cases hm : mark g n D a (z a) e = true
    · rw [hm]
      exact decide_eq_true (Finset.mem_filter.2 ⟨Finset.mem_range.2 he1, a, he2, hm⟩)
    · rw [Bool.not_eq_true] at hm
      rw [hm]
      refine decide_eq_false fun h => ?_
      obtain ⟨a', h1, h2⟩ := (Finset.mem_filter.1 h).2
      rw [mark_eq hz he1 h1 he2, hm] at h2
      exact Bool.false_ne_true h2
  refine ⟨σ, P, fun e he => ?_, funext fun a => ext_getD (by rw [length_st, hlen]) fun j hj => ?_⟩
  · obtain ⟨he1, a', h1, h2⟩ := Finset.mem_filter.1 he
    have he1' := Finset.mem_range.1 he1
    refine Finset.mem_filter.2 ⟨he1, vio_iff.2 fun l hl => ?_⟩
    have hlt := lit_lt hw he1' hl
    have ht : tchB g n D (l.1 / qv g n) e = true := tchB_iff.2 (Or.inl ⟨l, hl, rfl⟩)
    have hm : mark g n D (l.1 / qv g n) (z ⟨l.1 / qv g n, div_qv_lt hg hlt⟩) e = true := by
      rw [← h2]
      exact mark_eq hz he1' (a := ⟨l.1 / qv g n, div_qv_lt hg hlt⟩) ht h1
    have hb := (base_iff.1 (hz.1 ⟨l.1 / qv g n, div_qv_lt hg hlt⟩)).2 e (mem_tch.2 ⟨he1', ht⟩)
    rcases hb with hb | hb
    · rw [hm] at hb
      exact absurd hb (by simp)
    · rcases hb l hl with h | h
      · exact absurd rfl h
      · rw [ext_of_lt hlt]
        exact h
  · rw [length_st] at hj
    by_cases hjq : j < qv g n
    · rw [getD_st_lt _ _ _ hjq]
      by_cases hx : a.val * qv g n + j < n
      · rw [ext_of_lt hx]
        have e1 : (a.val * qv g n + j) / qv g n = a.val := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hjq, Nat.zero_add]
        have e2 : (a.val * qv g n + j) % qv g n = j := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hjq]
        show (z ⟨(a.val * qv g n + j) / qv g n, _⟩).getD ((a.val * qv g n + j) % qv g n) false = _
        have e3 : (⟨(a.val * qv g n + j) / qv g n, div_qv_lt hg hx⟩ : Fin g) = a := Fin.ext e1
        rw [e3, e2]
      · rw [ext_of_le (not_lt.1 hx)]
        exact (((base_iff.1 (hz.1 a)).1 j hjq).resolve_left hx).symm
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hjq)
      have ht : t < (tch g n D a).length := by omega
      rw [getD_st_ge _ _ _ ht, key a _ (List.getElem_mem ht), mark_getElem _ _ ht]
end VariableBound.Net.Val
