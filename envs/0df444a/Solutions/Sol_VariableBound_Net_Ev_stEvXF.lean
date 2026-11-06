-- Prove2me | solution 1 for VariableBound.Net.Ev.stEvXF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:44:55.945461+00:00
-- url     : https://prove2.me/submissions/47577bfe-e162-419d-b3aa-6df90d5b6c31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Net_Ev
import Theorems.Thm_VariableBound_Net_Ev_emod_eq_of_modEq
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
open VariableBound VariableBound.Net VariableBound.Net.Ev
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg
open ClauseBound.ParityChecks (Vof)
namespace VariableBound.Net.Ev
theorem _root_.solution (h : StEvD) (hXF : AppVariables.XFStmt) (hR : AppVariables.ResiduesStmt) (hC : StChks) : StEvXF := by
  intro Idx _ S ok hCor k pad i n Δ nb M D hok hK hF hprof hnet h1 h2
  have hlen : (chks D).length = D.2.length := (hC k n D hF.wf).1
  have hβ : 1 ≤ AppVariables.beta n D.1.length nb := by unfold AppVariables.beta; omega
  obtain ⟨hx, hf⟩ := hXF (Fin n → Bool) (Fin D.1.length) (Vof (n := n) D.1) nb (chks D) (AppVariables.beta n D.1.length nb) n M hβ (by rw [hlen]; exact h1) (by rw [hlen]; exact h2)
  obtain ⟨⟨hx0, hx1, hx2⟩, hf01⟩ := hR (Fin n → Bool) (Fin D.1.length) (Vof (n := n) D.1) nb (chks D) n (by simp)
  refine ⟨?_, fun h0 => ?_⟩
  · unfold evX
    rw [h Idx S ok hCor k pad i n Δ nb M false D hok hK hF hprof hnet]
    refine emod_eq_of_modEq hx hx0 (lt_of_le_of_lt (hx1.trans hx2) ?_)
    rw [Fintype.card_fin]
    have e : AppVariables.beta n D.1.length nb = n + Nat.clog 2 (D.1.length.choose (nb + 1)) + 1 := rfl
    have h4 : (0 : ℤ) < 2 ^ (n + Nat.clog 2 (D.1.length.choose (nb + 1))) := by positivity
    rw [e, pow_succ]; linarith
  · unfold evF
    rw [h Idx S ok hCor k pad i n Δ nb M true D hok hK hF hprof hnet]
    obtain ⟨hf0, hf1⟩ := hf01 h0
    refine emod_eq_of_modEq hf hf0 (lt_of_le_of_lt hf1 ?_)
    have h4 : (0 : ℤ) < 2 ^ n := by positivity
    rw [pow_succ]; linarith
end VariableBound.Net.Ev
