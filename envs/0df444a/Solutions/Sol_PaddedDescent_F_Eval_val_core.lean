-- Prove2me | solution 1 for PaddedDescent.F.Eval.val_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:08.200868+00:00
-- url     : https://prove2.me/submissions/cf30bb5c-8505-4baa-980f-5bd24cf48325

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_PaddedDescent_F_Eval
import Theorems.Thm_PaddedDescent_F_Eval_le_lamG
import Theorems.Thm_Groundwork_Colouring_beta_le
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Prog_NetE_Pc_le
import Theorems.Thm_Groundwork_Prog_NetE_Uc_eq
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
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Eval
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open PaddedDescent.F.Mark (Cl trunc Good nSat occ placeAt placeE layersE Asked MCtx markF markN adm nProf cls WfL)
namespace PaddedDescent.F.Eval
theorem _root_.solution (hR : StR) (hD : StD) {C : Type} (F : FNet C) (c : C) (pad : U) (sched : List Lvl) (K g Ub₀ P : ℕ) (hg : g = 3 * K ^ 8)
    (N : Network (Fin g) (List Bool) (List Bool)) (hK : 2 ≤ K) (chain : Chain K sched) (col : K ^ g ≤ pad.length)
    (st : 2 ^ (P * (2 * g / K)) ≤ pad.length) (lab : 2 ^ P ≤ pad.length) (tab : 2 ^ ((K - 1) * lamG K g Ub₀ P) ≤ pad.length)
    (fits : Fits pad.length K (lamG K g Ub₀ P) (P * (2 * g / K)) 1 sched) (hN : F.toP.Presents c N 0 0) (hS : N.Sized P 0)
    (hU : N.U ≤ Ub₀) : ((rebalF pad K g F c).elim 0 fun I => ((descend pad sched I).map (bruteF pad 256)).sum) = N.value := by
  have hK0 : 0 < K := by omega
  have hβ : betaC K g F.toP c ≤ lamG K g Ub₀ P := by
    have h1 := Colouring.beta_le K g (Uc g F.toP c) (Pc g F.toP c)
    exact le_lamG hK0 h1 (by rw [Uc_eq F.toP hN]; exact hU) (Pc_le F.toP hN hS)
  obtain ⟨J, hJ, hz, hlen, hWF⟩ := hR _ pad K g F c N P 0 hK hg.ge hN hS col st lab
    ((Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hβ)).trans tab)
  have hWF' : WF K (lamG K g Ub₀ P) (P * (2 * g / K)) J :=
    ⟨hWF.lam_pos, le_lamG hK0 hlen hU le_rfl, hWF.rows, hWF.row_len, by simpa using hWF.abs_le⟩
  rw [hJ]
  simp only [Option.elim]
  rw [hD pad sched K _ _ J chain fits hWF', hz]
end PaddedDescent.F.Eval
