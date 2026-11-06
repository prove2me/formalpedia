-- Prove2me | solution 1 for SplitCount.stStepThree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:28:18.515053+00:00
-- url     : https://prove2.me/submissions/21543fe5-9190-458f-9a6b-ec313fc77dd2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_Occ_Main
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_SplitCount_Width
import Theorems.Thm_Eight_Width_cntN_splitN
import Theorems.Thm_Eight_Width_numFresh_toN
import Theorems.Thm_Eight_Width_stWidth
import Theorems.Thm_Eight_Width_toN_widthReduce
import Theorems.Thm_GraphProblems_exists_toN
import Theorems.Thm_Groundwork_Decode_length_toN
import Theorems.Thm_Groundwork_Decode_mem_toN
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
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
attribute [local fun_prop] Groundwork.PolyT.map
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
open SplitCount
open Groundwork Groundwork.Prog CountKSat Eight.Width Occ
namespace SplitCount
theorem _root_.solution : StStepThree := by
  intro w n Ψ hw hb
  obtain ⟨φ, rfl⟩ := GraphProblems.exists_toN hb
  obtain ⟨⟨h3, hnd⟩, -, hk⟩ := stWidth n φ
  obtain ⟨hf, hl⟩ := hk w fun C hC => by
    have := hw _ (List.mem_map_of_mem hC)
    simpa using this
  have e1 : (widthP (List.replicate n (), Decode.toN φ)).1.length = n + numFresh φ := by simp [widthP, numFresh_toN]
  have e2 : (widthP (List.replicate n (), Decode.toN φ)).2 = Decode.toN (widthReduce φ) := by simp [widthP, toN_widthReduce]
  rw [e1, e2, Decode.length_toN, Decode.length_toN]
  refine ⟨fun C hC => ?_, below_toN _, ?_, by omega, hl, ?_⟩
  · obtain ⟨⟨D, hD, hDl⟩, -⟩ := Decode.mem_toN hC
    exact hDl ▸ h3 D hD
  · refine List.Nodup.map (List.map_injective_iff.2 fun a b hab => ?_) hnd
    exact Prod.ext (Fin.ext (Prod.ext_iff.1 hab).1) (Prod.ext_iff.1 hab).2
  · rw [toN_widthReduce, ← numFresh_toN, cntN_splitN]
end SplitCount
