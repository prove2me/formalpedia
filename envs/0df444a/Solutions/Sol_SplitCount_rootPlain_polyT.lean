-- Prove2me | solution 1 for SplitCount.rootPlain_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:20:52.498192+00:00
-- url     : https://prove2.me/submissions/706aff0a-94cf-40d2-8229-bcd0b68d54e4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_Occ_Main
import Definitions.Def_CountKSat_Walk
import Definitions.Def_CountKSat_Poly
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_SplitCount_Cert
import Theorems.Thm_CircuitLowerBound_Parse_decC_polyT
import Theorems.Thm_CircuitLowerBound_Parse_gateOfW_polyT
import Theorems.Thm_CircuitLowerBound_Parse_ones_polyT
import Theorems.Thm_CircuitLowerBound_Parse_ones_unary
import Theorems.Thm_CircuitLowerBound_Parse_rest_polyT
import Theorems.Thm_CircuitLowerBound_Parse_wfB_polyT
import Theorems.Thm_GraphProblems_adjB_polyT
import Theorems.Thm_GraphProblems_blockCl_polyT
import Theorems.Thm_GraphProblems_digit_polyT
import Theorems.Thm_GraphProblems_ones_polyT
import Theorems.Thm_GraphProblems_posC_polyT
import Theorems.Thm_GraphProblems_rest_polyT
import Theorems.Thm_Groundwork_DecodeK_clauseDec_polyT
import Theorems.Thm_Groundwork_Decode_clauseDec_polyT
import Theorems.Thm_Groundwork_Decode_slotDec_polyT
import Theorems.Thm_Groundwork_Decode_width_polyT
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_comp
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
import Theorems.Thm_Groundwork_Prog_Count_linkB_polyT
import Theorems.Thm_Groundwork_Prog_Count_links_polyT
import Theorems.Thm_Groundwork_Prog_Count_litAt_polyT
import Theorems.Thm_Groundwork_Prog_Count_locals_polyT
import Theorems.Thm_Groundwork_Prog_Count_mu_polyT
import Theorems.Thm_Groundwork_Prog_Count_rows_polyT
import Theorems.Thm_Groundwork_Prog_Count_slotsOf_polyT
import Theorems.Thm_Groundwork_Prog_Count_varAt_polyT
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
import Theorems.Thm_Groundwork_Sparsify_polyT_addP
import Theorems.Thm_Groundwork_Sparsify_polyT_canonP
import Theorems.Thm_Groundwork_Sparsify_polyT_greedyP
import Theorems.Thm_Groundwork_Sparsify_polyT_litsOf
import Theorems.Thm_Groundwork_Sparsify_polyT_minusP
import Theorems.Thm_Groundwork_Sparsify_polyT_overP
import Theorems.Thm_Groundwork_Sparsify_polyT_pickP
import Theorems.Thm_Groundwork_Sparsify_polyT_redP
import Theorems.Thm_Groundwork_Sparsify_polyT_rootP
import Theorems.Thm_Groundwork_Sparsify_polyT_stepP
import Theorems.Thm_Groundwork_Sparsify_polyT_subP
import Theorems.Thm_Groundwork_block_polyT
import Theorems.Thm_Groundwork_digit_polyT
import Theorems.Thm_Groundwork_query0_polyT
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
import Theorems.Thm_PaddedDescent_F_cap_polyT
import Theorems.Thm_WidthK_Prog_polyT_heartsP
import Theorems.Thm_WidthK_Prog_polyT_maskP
import Theorems.Thm_WidthK_Prog_polyT_pickK
import Theorems.Thm_WidthK_Prog_polyT_stepK
import Theorems.Thm_WidthK_Prog_polyT_tryT
attribute [local fun_prop] CircuitLowerBound.Parse.decC_polyT
attribute [local fun_prop] CircuitLowerBound.Parse.gateOfW_polyT
attribute [local fun_prop] CircuitLowerBound.Parse.ones_polyT
attribute [local fun_prop] CircuitLowerBound.Parse.ones_unary
attribute [local fun_prop] CircuitLowerBound.Parse.rest_polyT
attribute [local fun_prop] CircuitLowerBound.Parse.wfB_polyT
attribute [local fun_prop] GraphProblems.adjB_polyT
attribute [local fun_prop] GraphProblems.blockCl_polyT
attribute [local fun_prop] GraphProblems.digit_polyT
attribute [local fun_prop] GraphProblems.ones_polyT
attribute [local fun_prop] GraphProblems.posC_polyT
attribute [local fun_prop] GraphProblems.rest_polyT
attribute [local fun_prop] Groundwork.Decode.clauseDec_polyT
attribute [local fun_prop] Groundwork.Decode.slotDec_polyT
attribute [local fun_prop] Groundwork.Decode.width_polyT
attribute [local fun_prop] Groundwork.DecodeK.clauseDec_polyT
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
attribute [local fun_prop] Groundwork.Prog.Count.linkB_polyT
attribute [local fun_prop] Groundwork.Prog.Count.links_polyT
attribute [local fun_prop] Groundwork.Prog.Count.litAt_polyT
attribute [local fun_prop] Groundwork.Prog.Count.locals_polyT
attribute [local fun_prop] Groundwork.Prog.Count.mu_polyT
attribute [local fun_prop] Groundwork.Prog.Count.rows_polyT
attribute [local fun_prop] Groundwork.Prog.Count.slotsOf_polyT
attribute [local fun_prop] Groundwork.Prog.Count.varAt_polyT
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
attribute [local fun_prop] Groundwork.Sparsify.polyT_addP
attribute [local fun_prop] Groundwork.Sparsify.polyT_canonP
attribute [local fun_prop] Groundwork.Sparsify.polyT_greedyP
attribute [local fun_prop] Groundwork.Sparsify.polyT_litsOf
attribute [local fun_prop] Groundwork.Sparsify.polyT_minusP
attribute [local fun_prop] Groundwork.Sparsify.polyT_overP
attribute [local fun_prop] Groundwork.Sparsify.polyT_pickP
attribute [local fun_prop] Groundwork.Sparsify.polyT_redP
attribute [local fun_prop] Groundwork.Sparsify.polyT_rootP
attribute [local fun_prop] Groundwork.Sparsify.polyT_stepP
attribute [local fun_prop] Groundwork.Sparsify.polyT_subP
attribute [local fun_prop] Groundwork.block_polyT
attribute [local fun_prop] Groundwork.digit_polyT
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
attribute [local fun_prop] PaddedDescent.F.cap_polyT
attribute [local fun_prop] WidthK.Prog.polyT_heartsP
attribute [local fun_prop] WidthK.Prog.polyT_maskP
attribute [local fun_prop] WidthK.Prog.polyT_pickK
attribute [local fun_prop] WidthK.Prog.polyT_stepK
attribute [local fun_prop] WidthK.Prog.polyT_tryT



set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Stepped Paper CountKSat Eight.Width Occ
namespace SplitCount
theorem _root_.solution : PolyT rootPlain := by
  unfold rootPlain
  fun_prop
end SplitCount
