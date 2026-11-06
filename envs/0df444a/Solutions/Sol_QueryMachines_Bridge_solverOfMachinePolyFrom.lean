-- Prove2me | solution 1 for QueryMachines.Bridge.solverOfMachinePolyFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:25:12.284444+00:00
-- url     : https://prove2.me/submissions/d6d63280-1e15-4c02-a4be-b5e2e71dbc23

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Tables
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_CountedToPadded_SolverPoly
import Theorems.Thm_QueryMachines_Bridge_Proof_needOf_poly
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_contains
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_decide_mem
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_div_pow
import Theorems.Thm_Groundwork_PolyT_dropWhile
import Theorems.Thm_Groundwork_PolyT_elem
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_optionElim
import Theorems.Thm_Groundwork_PolyT_pow_const
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_product
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sprod
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_PolyT_sumElim
import Theorems.Thm_Groundwork_PolyT_takeWhile
import Theorems.Thm_Groundwork_PolyT_testBit
import Theorems.Thm_Groundwork_Prog_NetE_Pc_polyT
import Theorems.Thm_Groundwork_Prog_NetE_betaC_polyT
import Theorems.Thm_Groundwork_Prog_NetE_capWord_polyT
import Theorems.Thm_Groundwork_Prog_NetE_cap_polyT
import Theorems.Thm_Groundwork_Prog_NetE_col_polyT
import Theorems.Thm_Groundwork_Prog_NetE_lAt_polyT
import Theorems.Thm_Groundwork_Prog_NetE_labOf_polyT
import Theorems.Thm_Groundwork_Prog_NetE_lbLen_polyT
import Theorems.Thm_Groundwork_Prog_NetE_lbLens_polyT
import Theorems.Thm_Groundwork_Prog_NetE_members_polyT
import Theorems.Thm_Groundwork_Prog_NetE_n_polyT
import Theorems.Thm_Groundwork_Prog_NetE_prs_polyT
import Theorems.Thm_Groundwork_Prog_NetE_stLens_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zA_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zAt_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zOf_polyT
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
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_block_polyT
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_query0_polyT
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
import Theorems.Thm_Groundwork_tri_polyT
import Theorems.Thm_P2M_Groundwork_PolyT_chunks__bc5b8682856d
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_inl__78f4b62d65a1
import Theorems.Thm_P2M_Groundwork_PolyT_inr__53ca1f30b2d3
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_log2__935ea318e2e8
import Theorems.Thm_P2M_Groundwork_PolyT_ofWord__0eb069943014
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
import Theorems.Thm_PaddedDescent_F_CertNet_Pc2
import Theorems.Thm_PaddedDescent_F_CertNet_UcU
import Theorems.Thm_PaddedDescent_F_CertNet_betaC2
import Theorems.Thm_PaddedDescent_F_CertNet_betaCU
import Theorems.Thm_PaddedDescent_F_CertNet_capP
import Theorems.Thm_PaddedDescent_F_CertNet_capU
import Theorems.Thm_PaddedDescent_F_CertNet_col2
import Theorems.Thm_PaddedDescent_F_CertNet_goodB2
import Theorems.Thm_PaddedDescent_F_CertNet_isOne2
import Theorems.Thm_PaddedDescent_F_CertNet_isPsi2
import Theorems.Thm_PaddedDescent_F_CertNet_isW2
import Theorems.Thm_PaddedDescent_F_CertNet_lAt2
import Theorems.Thm_PaddedDescent_F_CertNet_labOf2
import Theorems.Thm_PaddedDescent_F_CertNet_lbLen2
import Theorems.Thm_PaddedDescent_F_CertNet_lbLens2
import Theorems.Thm_PaddedDescent_F_CertNet_look_polyT
import Theorems.Thm_PaddedDescent_F_CertNet_members2
import Theorems.Thm_PaddedDescent_F_CertNet_nLab2
import Theorems.Thm_PaddedDescent_F_CertNet_nP
import Theorems.Thm_PaddedDescent_F_CertNet_nStates2
import Theorems.Thm_PaddedDescent_F_CertNet_nU
import Theorems.Thm_PaddedDescent_F_CertNet_prs2
import Theorems.Thm_PaddedDescent_F_CertNet_qF2
import Theorems.Thm_PaddedDescent_F_CertNet_qP12
import Theorems.Thm_PaddedDescent_F_CertNet_qP22
import Theorems.Thm_PaddedDescent_F_CertNet_qW2
import Theorems.Thm_PaddedDescent_F_CertNet_rowSumU
import Theorems.Thm_PaddedDescent_F_CertNet_stLenU
import Theorems.Thm_PaddedDescent_F_CertNet_stLens2
import Theorems.Thm_PaddedDescent_F_CertNet_validB2
import Theorems.Thm_PaddedDescent_F_CertNet_zA2
import Theorems.Thm_PaddedDescent_F_CertNet_zAt2
import Theorems.Thm_PaddedDescent_F_CertNet_zOf2
import Theorems.Thm_PaddedDescent_F_cap_polyT
import Theorems.Thm_QueryMachines_Bridge_Proof_bitsOfTables_unary
import Theorems.Thm_QueryMachines_Bridge_Proof_len_tab_unary
import Theorems.Thm_QueryMachines_QueryMachine_close_bind
import Theorems.Thm_QueryMachines_QueryMachine_close_both
import Theorems.Thm_QueryMachines_QueryMachine_close_branch
import Theorems.Thm_QueryMachines_QueryMachine_close_const
import Theorems.Thm_QueryMachines_QueryMachine_close_foldRange
import Theorems.Thm_QueryMachines_QueryMachine_close_foldWhile
import Theorems.Thm_QueryMachines_QueryMachine_close_gated
import Theorems.Thm_QueryMachines_QueryMachine_close_ite
import Theorems.Thm_QueryMachines_QueryMachine_close_lift
import Theorems.Thm_QueryMachines_QueryMachine_close_mapAsk
import Theorems.Thm_QueryMachines_QueryMachine_close_mapIn
import Theorems.Thm_QueryMachines_QueryMachine_close_mapOut
import Theorems.Thm_QueryMachines_QueryMachine_close_optBind
import Theorems.Thm_QueryMachines_QueryMachine_close_prodRange
import Theorems.Thm_QueryMachines_QueryMachine_close_query
import Theorems.Thm_QueryMachines_QueryMachine_close_subst
import Theorems.Thm_QueryMachines_QueryMachine_close_sumRange
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.contains
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.decide_mem
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.div_pow
attribute [local fun_prop] Groundwork.PolyT.dropWhile
attribute [local fun_prop] Groundwork.PolyT.elem
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.mod
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.pow_const
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.product
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sprod
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] Groundwork.PolyT.takeWhile
attribute [local fun_prop] Groundwork.PolyT.testBit
attribute [local fun_prop] Groundwork.Prog.NetE.Pc_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.betaC_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.capWord_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.cap_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.col_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.lAt_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.labOf_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.lbLen_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.lbLens_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.members_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.n_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.prs_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.stLens_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.zA_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.zAt_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.zOf_polyT
attribute [local fun_prop] Groundwork.block_polyT
attribute [local fun_prop] Groundwork.query0_polyT
attribute [local fun_prop] Groundwork.tri_polyT
attribute [local fun_prop] P2M_Groundwork_PolyT_chunks__bc5b8682856d
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_inl__78f4b62d65a1
attribute [local fun_prop] P2M_Groundwork_PolyT_inr__53ca1f30b2d3
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_log2__935ea318e2e8
attribute [local fun_prop] P2M_Groundwork_PolyT_ofWord__0eb069943014
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f
attribute [local fun_prop] P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local fun_prop] PaddedDescent.F.CertNet.Pc2
attribute [local fun_prop] PaddedDescent.F.CertNet.UcU
attribute [local fun_prop] PaddedDescent.F.CertNet.betaC2
attribute [local fun_prop] PaddedDescent.F.CertNet.betaCU
attribute [local fun_prop] PaddedDescent.F.CertNet.capP
attribute [local fun_prop] PaddedDescent.F.CertNet.capU
attribute [local fun_prop] PaddedDescent.F.CertNet.col2
attribute [local fun_prop] PaddedDescent.F.CertNet.goodB2
attribute [local fun_prop] PaddedDescent.F.CertNet.isOne2
attribute [local fun_prop] PaddedDescent.F.CertNet.isPsi2
attribute [local fun_prop] PaddedDescent.F.CertNet.isW2
attribute [local fun_prop] PaddedDescent.F.CertNet.lAt2
attribute [local fun_prop] PaddedDescent.F.CertNet.labOf2
attribute [local fun_prop] PaddedDescent.F.CertNet.lbLen2
attribute [local fun_prop] PaddedDescent.F.CertNet.lbLens2
attribute [local fun_prop] PaddedDescent.F.CertNet.look_polyT
attribute [local fun_prop] PaddedDescent.F.CertNet.members2
attribute [local fun_prop] PaddedDescent.F.CertNet.nLab2
attribute [local fun_prop] PaddedDescent.F.CertNet.nP
attribute [local fun_prop] PaddedDescent.F.CertNet.nStates2
attribute [local fun_prop] PaddedDescent.F.CertNet.nU
attribute [local fun_prop] PaddedDescent.F.CertNet.prs2
attribute [local fun_prop] PaddedDescent.F.CertNet.qF2
attribute [local fun_prop] PaddedDescent.F.CertNet.qP12
attribute [local fun_prop] PaddedDescent.F.CertNet.qP22
attribute [local fun_prop] PaddedDescent.F.CertNet.qW2
attribute [local fun_prop] PaddedDescent.F.CertNet.rowSumU
attribute [local fun_prop] PaddedDescent.F.CertNet.stLenU
attribute [local fun_prop] PaddedDescent.F.CertNet.stLens2
attribute [local fun_prop] PaddedDescent.F.CertNet.validB2
attribute [local fun_prop] PaddedDescent.F.CertNet.zA2
attribute [local fun_prop] PaddedDescent.F.CertNet.zAt2
attribute [local fun_prop] PaddedDescent.F.CertNet.zOf2
attribute [local fun_prop] PaddedDescent.F.cap_polyT
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
attribute [local simp] QueryMachines.QueryMachine.close_bind
attribute [local simp] QueryMachines.QueryMachine.close_both
attribute [local simp] QueryMachines.QueryMachine.close_branch
attribute [local simp] QueryMachines.QueryMachine.close_const
attribute [local simp] QueryMachines.QueryMachine.close_foldRange
attribute [local simp] QueryMachines.QueryMachine.close_foldWhile
attribute [local simp] QueryMachines.QueryMachine.close_gated
attribute [local simp] QueryMachines.QueryMachine.close_ite
attribute [local simp] QueryMachines.QueryMachine.close_lift
attribute [local simp] QueryMachines.QueryMachine.close_mapAsk
attribute [local simp] QueryMachines.QueryMachine.close_mapIn
attribute [local simp] QueryMachines.QueryMachine.close_mapOut
attribute [local simp] QueryMachines.QueryMachine.close_optBind
attribute [local simp] QueryMachines.QueryMachine.close_prodRange
attribute [local simp] QueryMachines.QueryMachine.close_query
attribute [local simp] QueryMachines.QueryMachine.close_subst
attribute [local simp] QueryMachines.QueryMachine.close_sumRange



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge
open Groundwork Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed Proof
namespace QueryMachines.Bridge
theorem _root_.solution : SolverOfMachinePolyFrom := by
  intro hRun M _ num C₀ hnum
  have hneed := needOf_poly hnum C₀
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := @hRun _ _ _ _ (onTables M) (onTablesIsPoly M)
    have hroom : Unary fun x : U × (U × U) × PInst => 7 * x.1.length + 14 * len x.2.2.2 + 2 :=
      (((Unary.const 7).mul (Unary.of_length (by fun_prop))).add ((Unary.const 14).mul (len_tab_unary.comp (by fun_prop)))).add (Unary.const 2)
    have hbits : PolyT fun x : U × (U × U) × PInst => unary (bitsOfTables x.2.2.2) := Unary.comp bitsOfTables_unary (by fun_prop)
    have hc := PolyT.comp h (PolyT.prodMk (PolyT.prodMk (by fun_prop : PolyT fun x : U × (U × U) × PInst => x.1) hroom)
      (PolyT.prodMk (by fun_prop : PolyT fun x : U × (U × U) × PInst => x.2.2.2) (PolyT.prodMk (by fun_prop : PolyT fun x : U × (U × U) × PInst => x.2.1.1)
        (PolyT.prodMk (by fun_prop : PolyT fun x : U × (U × U) × PInst => x.2.2.1) hbits))))
    refine (PolyT.optionGetD hc (PolyT.const 0)).congr fun x => ?_
    simp only [List.length_replicate]
    rfl
  · exact (Unary.of_length (by fun_prop : PolyT fun i : U × U => i.2) : Unary fun i : U × U => i.2.length)
  · show PolyT fun x : U × (U × U) × U × U => if needOf num C₀ x.2 ≤ x.1.length then some (needOf num C₀ x.2) else none
    generalize needOf num C₀ = f at hneed ⊢
    fun_prop
  · intro b x v h
    replace h : (if needOf num C₀ x ≤ b.length then some (needOf num C₀ x) else none) = some v := h
    split at h
    · exact (Option.some.inj h).symm
    · cases h
  · intro b x h
    exact if_pos h
end QueryMachines.Bridge
