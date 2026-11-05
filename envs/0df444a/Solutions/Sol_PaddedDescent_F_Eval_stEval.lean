-- Prove2me | solution 1 for PaddedDescent.F.Eval.stEval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:21.558543+00:00
-- url     : https://prove2.me/submissions/e7b42451-a4b2-4c37-8dec-0292571cef63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_PaddedDescent_F_Eval
import Theorems.Thm_PaddedDescent_F_Eval_length_gU
import Theorems.Thm_PaddedDescent_F_Eval_length_cls
import Theorems.Thm_PaddedDescent_F_Eval_nProf_le
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
import Theorems.Thm_PaddedDescent_F_sumF_eq
attribute [local fun_prop] Groundwork.PolyT.length
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
theorem _root_.solution (hV : StValF) (hP : StMarkPresents) (hSum : StMarkSum) (hSz : StMarkSized) : StEval := by
  intro k pad S p Ls R₁ Δ m hNet hProf hb0 hb hm hW hocc hlen hR₁
  obtain ⟨nu, wu, βu, bu⟩ := p
  simp only at hNet hb0 hb hm hW ⊢
  have hg := length_gU S.2
  have hg0 : 0 < (gU S.2).length := by
    have : 0 < S.2.length ^ 8 := Nat.pow_pos (by have := hNet.two_le; omega)
    omega
  unfold evalF
  rw [sumF_eq ((nProf_le _ ((length_cls Ls).le.trans hlen) hR₁).trans (by rw [hg]; exact hProf)),
    ← hSum k (gU S.2) nu βu bu wu.length Ls hg0 hb0 hb hW]
  refine Finset.sum_congr rfl fun y _ => ?_
  cases hy : adm k (gU S.2).length nu.length wu.length Ls y with
  | false => simp
  | true =>
    obtain ⟨s1, s2⟩ := hSz k (gU S.2) nu βu bu wu.length Δ Ls y hg0 hb0 hb hW hocc (hlen.trans hm) hy
    have hUb : Ub k (gU S.2).length nu.length wu.length βu.length Ls.length ≤ Ub k (gU S.2).length nu.length wu.length βu.length R₁ :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hR₁)
    rw [← hg] at hNet
    simpa using hV _ markF ((gU S.2, nu, βu, bu), (Ls, y)) pad S _ _ (markN (gU S.2).length ((gU S.2, nu, βu, bu), (Ls, y))) hNet
      (hP _) s1 (s2.trans hUb)
end PaddedDescent.F.Eval
