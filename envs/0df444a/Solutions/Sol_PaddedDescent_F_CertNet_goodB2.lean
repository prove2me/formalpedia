-- Prove2me | solution 1 for PaddedDescent.F.CertNet.goodB2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:56:42.011962+00:00
-- url     : https://prove2.me/submissions/6a8f7375-f7a6-4733-9e04-300271602c59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertNet
import Theorems.Thm_PaddedDescent_F_CertNet_col2
import Theorems.Thm_PaddedDescent_F_CertNet_members2
import Theorems.Thm_PaddedDescent_F_CertNet_prs2
import Theorems.Thm_PaddedDescent_F_CertNet_nU
import Theorems.Thm_PaddedDescent_F_CertNet_capU
import Theorems.Thm_PaddedDescent_F_CertNet_nP
import Theorems.Thm_PaddedDescent_F_CertNet_capP
import Theorems.Thm_PaddedDescent_F_CertNet_stLens2
import Theorems.Thm_PaddedDescent_F_CertNet_stLenU
import Theorems.Thm_PaddedDescent_F_CertNet_zAt2
import Theorems.Thm_PaddedDescent_F_CertNet_lbLens2
import Theorems.Thm_PaddedDescent_F_CertNet_lbLen2
import Theorems.Thm_PaddedDescent_F_CertNet_lAt2
import Theorems.Thm_PaddedDescent_F_CertNet_validB2
import Theorems.Thm_PaddedDescent_F_CertNet_zOf2
import Theorems.Thm_PaddedDescent_F_CertNet_zA2
import Theorems.Thm_PaddedDescent_F_CertNet_labOf2
import Theorems.Thm_PaddedDescent_F_CertNet_qW2
import Theorems.Thm_PaddedDescent_F_CertNet_qF2
import Theorems.Thm_PaddedDescent_F_CertNet_qP12
import Theorems.Thm_PaddedDescent_F_CertNet_qP22
import Theorems.Thm_PaddedDescent_F_CertNet_nLab2
import Theorems.Thm_PaddedDescent_F_CertNet_nStates2
import Theorems.Thm_PaddedDescent_F_CertNet_isOne2
import Theorems.Thm_PaddedDescent_F_CertNet_isW2
import Theorems.Thm_PaddedDescent_F_CertNet_isPsi2
import Theorems.Thm_PaddedDescent_F_CertNet_rowSumU
import Theorems.Thm_PaddedDescent_F_CertNet_UcU
import Theorems.Thm_PaddedDescent_F_CertNet_Pc2
import Theorems.Thm_PaddedDescent_F_CertNet_betaC2
import Theorems.Thm_PaddedDescent_F_CertNet_betaCU
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
import Theorems.Thm_Groundwork_Unary_poly
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


attribute [local fun_prop] PaddedDescent.F.CertNet.col2
attribute [local fun_prop] PaddedDescent.F.CertNet.members2
attribute [local fun_prop] PaddedDescent.F.CertNet.prs2
attribute [local fun_prop] PaddedDescent.F.CertNet.nU
attribute [local fun_prop] PaddedDescent.F.CertNet.capU
attribute [local fun_prop] PaddedDescent.F.CertNet.nP
attribute [local fun_prop] PaddedDescent.F.CertNet.capP
attribute [local fun_prop] PaddedDescent.F.CertNet.stLens2
attribute [local fun_prop] PaddedDescent.F.CertNet.stLenU
attribute [local fun_prop] PaddedDescent.F.CertNet.zAt2
attribute [local fun_prop] PaddedDescent.F.CertNet.lbLens2
attribute [local fun_prop] PaddedDescent.F.CertNet.lbLen2
attribute [local fun_prop] PaddedDescent.F.CertNet.lAt2
attribute [local fun_prop] PaddedDescent.F.CertNet.validB2
attribute [local fun_prop] PaddedDescent.F.CertNet.zOf2
attribute [local fun_prop] PaddedDescent.F.CertNet.zA2
attribute [local fun_prop] PaddedDescent.F.CertNet.labOf2
attribute [local fun_prop] PaddedDescent.F.CertNet.qW2
attribute [local fun_prop] PaddedDescent.F.CertNet.qF2
attribute [local fun_prop] PaddedDescent.F.CertNet.qP12
attribute [local fun_prop] PaddedDescent.F.CertNet.qP22
attribute [local fun_prop] PaddedDescent.F.CertNet.nLab2
attribute [local fun_prop] PaddedDescent.F.CertNet.nStates2
attribute [local fun_prop] PaddedDescent.F.CertNet.isOne2
attribute [local fun_prop] PaddedDescent.F.CertNet.isW2
attribute [local fun_prop] PaddedDescent.F.CertNet.isPsi2
attribute [local fun_prop] PaddedDescent.F.CertNet.rowSumU
attribute [local fun_prop] PaddedDescent.F.CertNet.UcU
attribute [local fun_prop] PaddedDescent.F.CertNet.Pc2
attribute [local fun_prop] PaddedDescent.F.CertNet.betaC2
attribute [local fun_prop] PaddedDescent.F.CertNet.betaCU

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertNet
open Groundwork Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F
variable {α β γ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc ε]
variable {C : Type} [Enc C] {Np : PNet C}
variable (h : KeepsU Np)
include h
namespace PaddedDescent.F.CertNet
theorem _root_.solution {K g : α → ℕ} {cx : α → C × ℕ} (hK : Unary K) (hg : Unary g) (hc : PolyT cx) :
    PolyT fun t => goodB (K t) (g t) Np (cx t) := by
  have hKp := hK.poly
  have hgp := hg.poly
  have h1 : PolyT fun t => (List.range (K t)).all fun G =>
      decide (K t * (members (K t) (g t) (cx t).2 G).length < 2 * g t) := by fun_prop
  have hb : PolyT fun q : (α × ℕ) × ℕ => betaC (K q.1.1) (g q.1.1) Np (cx q.1.1).1 :=
    betaC2 h (by fun_prop) (by fun_prop) (by fun_prop)
  have hl : PolyT fun q : (α × ℕ) × ℕ => lbLen (K q.1.1) (g q.1.1) Np (cx q.1.1).1 (cx q.1.1).2 q.1.2 q.2 :=
    lbLen2 h (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 : PolyT fun t => (List.range (K t)).all fun G => (List.range (K t)).all fun G' =>
      G == G' || decide (lbLen (K t) (g t) Np (cx t).1 (cx t).2 G G' ≤ betaC (K t) (g t) Np (cx t).1) :=
    PolyT.all (f := fun t G => (List.range (K t)).all fun G' =>
        G == G' || decide (lbLen (K t) (g t) Np (cx t).1 (cx t).2 G G' ≤ betaC (K t) (g t) Np (cx t).1))
      (PolyT.all (f := fun (q : α × ℕ) G' =>
          q.2 == G' || decide (lbLen (K q.1) (g q.1) Np (cx q.1).1 (cx q.1).2 q.2 G' ≤ betaC (K q.1) (g q.1) Np (cx q.1).1))
        (PolyT.or' (by fun_prop) (PolyT.decide_le hl hb)) (by fun_prop)) (by fun_prop)
  unfold goodB
  exact PolyT.and' h1 h2
end PaddedDescent.F.CertNet
