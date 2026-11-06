-- Prove2me | solution 1 for VariableBound.stCountD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:07:47.888189+00:00
-- url     : https://prove2.me/submissions/f84813bd-db55-4397-9d00-58f9d51ef955

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Count_Correct
import Theorems.Thm_VariableBound_Count_lg_le_LD
import Theorems.Thm_VariableBound_Count_sq_le
import Theorems.Thm_VariableBound_Count_row_le
import Theorems.Thm_VariableBound_Count_len_le
import Theorems.Thm_VariableBound_Count_evF_eq
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_tb_le
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
open VariableBound
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset
namespace VariableBound
theorem _root_.solution (hEv : Net.StEvXF) (hFit : Net.StFit) (hTb : Net.StTbMax) (hNP : Net.StNPrMax) (hS : StSearchD) (hFam : Fld.StFamD) (hSpec : StParamSpec)
    (hIneq : ParamIneq) (hProd : AppVariables.ProductStmt) (hEmpty : AppVariables.EmptyListStmt) : StCountD := by
  intro Idx _ S ok hC k pad i n Δ ψ hok hK hwf hocc hm hΔ hn hfit
  have hlg := Count.lg_le_LD Δ (by omega)
  have hsq : (2 * Δ) ^ 2 ≤ 2 ^ n := Count.sq_le n Δ (by omega)
  have h2Δ : 2 * Δ ≤ 2 ^ n := le_trans (by nlinarith) hsq
  have hNb : IsNb n Δ (nbD n Δ) := hSpec.1 n Δ (by omega) h2Δ
  have hnb2 : 2 ≤ nbD n Δ := hSpec.2.1 n Δ (by omega) hsq
  have hRb : IsRb (beta n ψ.length (nbD n Δ)) (rbD (beta n ψ.length (nbD n Δ))) := hSpec.2.2.1 _
  have hTbI : IsTb ψ.length (nbD n Δ) (rbD (beta n ψ.length (nbD n Δ))) (tbD ψ.length (nbD n Δ) (rbD (beta n ψ.length (nbD n Δ)))) := hSpec.2.2.2 _ _ _ hnb2
  have hnR : (29 : ℝ) * LD Δ + 19 ≤ n := by exact_mod_cast hn
  simp only [countD]
  generalize nbD n Δ = nb at *
  generalize hβ : beta n ψ.length nb = β at *
  generalize rbD β = rb at *
  generalize tbD ψ.length nb rb = tb at *
  have hβn : n + 1 ≤ β := by rw [← hβ]; unfold beta; omega
  have hM : Mb β rb = rb + β - 1 := rfl
  by_cases hc : ψ.length ≤ nb
  · rw [decide_eq_true hc, cond_true]
    have hβ1 : β = n + 1 := by
      rw [← hβ]; unfold beta
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.clog_of_right_le_one (by omega)]
    have hr := hIneq.rb_le β rb hRb
    have hr' : (rb : ℝ) ≤ 13 * n - 1 := by
      rw [hβ1] at hr; push_cast at hr
      have : (0 : ℝ) ≤ LD Δ := by positivity
      linarith
    have hr'' : rb + 1 ≤ 13 * n := by
      have : ((rb + 1 : ℕ) : ℝ) ≤ ((13 * n : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hF := (hFit k n Δ nb rb tb (Mb β rb) ψ [] hwf hΔ hocc hm hNb (by rw [hM]; omega)).2 hc
    refine Count.evF_eq hEv hNP hProd hC hok hK hfit hF (by rw [hβ, hM, List.length_nil]; omega) (by rw [hM, List.length_nil]; omega) ?_
    exact hEmpty (Fin n → Bool) (Fin ψ.length) (Vof (n := n) ψ) nb (by rw [Fintype.card_fin]; exact hc)
  · rw [decide_eq_false hc, cond_false]
    have hlt : nb < ψ.length := by omega
    obtain ⟨hrb10, hM14⟩ := hIneq.large n Δ ψ.length nb rb hΔ hlt hm hNb (by rw [hβ]; exact hRb) (by linarith)
    rw [hβ] at hM14
    have htb : tb ≤ tbMax n Δ := hTb n Δ ψ.length tb (by omega) hm (hIneq.tb_le n Δ ψ.length nb rb tb hΔ (by omega) hNb hrb10 hTbI)
    have hfitL : ∀ L, StructD ψ.length nb rb tb L → Fit k n Δ nb (Mb β rb) (ψ, L) := fun L hL =>
      (hFit k n Δ nb rb tb (Mb β rb) ψ L hwf hΔ hocc hm hNb hM14).1 hlt hL hrb10 (by rw [hM]; omega) (by rw [hM]; omega) htb
    have hl1 : ∀ L, StructD ψ.length nb rb tb L → beta n ψ.length nb - 1 + L.length ≤ Mb β rb := fun L hL => by
      have := hL.1; rw [hβ, hM]; omega
    have hl2 : ∀ L, StructD ψ.length nb rb tb L → n + L.length ≤ Mb β rb := fun L hL => by
      have := hL.1; rw [hM]; omega
    obtain ⟨a, ha⟩ := hNb.1
    have hlog : Nat.log 2 nb = a := by rw [ha]; exact Nat.log_pow (by norm_num) a
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · rw [ha, h] at hnb2; norm_num at hnb2
      · exact h
    obtain ⟨hne, -, hinc, hfam⟩ := hFam ψ.length a ha1 (by rw [← ha]; omega)
    rw [hlog]
    rw [← ha] at hfam
    have hres := hS (Fin n → Bool) ψ.length (Vof (n := n) ψ) n nb rb tb pad (fun L => evX S k pad i n Δ nb (Mb β rb) β (ψ, L)) (Fld.famD ψ.length a)
      (by simp) (by omega) (by rw [hβ]; exact hRb) hTbI hne (fun l hl => ⟨(hinc l hl).1, (hinc l hl).2.2⟩) hfam
      (fun L hL => by
        have := (hEv Idx S ok hC k pad i n Δ nb (Mb β rb) (ψ, L) hok hK (hfitL L hL) ((hNP k (S.K i) n Δ nb (Mb β rb) (ψ, L) (hfitL L hL)).trans hfit.prof) hfit.net
          (hl1 L hL) (hl2 L hL)).1
        have e : beta n (ψ, L).1.length nb = β := hβ
        rw [e] at this; exact this)
      (fun L hL => by
        refine (Count.len_le (10 * n) (sbMax Δ) (Δ * n) L (hL.1.trans hrb10) fun l hl => ⟨?_, fun E hE => ?_⟩).trans hfit.lists
        · exact Count.row_le hIneq n Δ ψ.length nb l.length hΔ hm hNb (hL.2.1 l hl).2.2
        · exact (Nat.le_of_lt ((hL.2.1 l hl).2.1 E hE)).trans hm)
    rw [hβ] at hres
    exact Count.evF_eq hEv hNP hProd hC hok hK hfit (hfitL _ hres.1) (hl1 _ hres.1) (hl2 _ hres.1) hres.2
end VariableBound
