-- Prove2me | solution 1 for VariableBound.Count.countD_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:09:33.396841+00:00
-- url     : https://prove2.me/submissions/72ee0ed3-3133-41ab-8776-26708b86da68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_VariableBound_Count_Cert
import Theorems.Thm_VariableBound_Count_log_unary
import Theorems.Thm_VariableBound_Count_evX_polyT
import Theorems.Thm_VariableBound_Count_evF_polyT
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
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
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_poly
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
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
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
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg AppVariables VariableBound.Net
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
namespace VariableBound.Count
theorem _root_.solution (hEv : Net.StCertEvD) (hS : StCertSearchD) (hFam : Fld.StCertFamD) (hPar : StCertParam) (hP : S.Poly) {k n Δ : α → ℕ} {pad : α → U} {i : α → Idx}
    {ψ : α → Fml} (hk : Unary k) (hn : Unary n) (hΔ : Unary Δ) (hp : PolyT pad) (hi : PolyT i) (hψ : PolyT ψ) :
    PolyT fun x => countD S (k x) (pad x) (i x) (n x) (Δ x) (ψ x) := by
  have hm : Unary fun x => (ψ x).length := Unary.of_length hψ
  have hnb : Unary fun x => nbD (n x) (Δ x) := (hPar α n Δ n n n n hn hΔ hn hn hn hn).1
  have hβ : Unary fun x => beta (n x) (ψ x).length (nbD (n x) (Δ x)) := (hPar α n Δ _ n _ n hn hΔ hm hn hnb hn).2.1
  have hrb : Unary fun x => rbD (beta (n x) (ψ x).length (nbD (n x) (Δ x))) := (hPar α n Δ n _ n n hn hΔ hn hβ hn hn).2.2.1
  have htb : Unary fun x => tbD (ψ x).length (nbD (n x) (Δ x)) (rbD (beta (n x) (ψ x).length (nbD (n x) (Δ x)))) :=
    (hPar α n Δ _ n _ _ hn hΔ hm hn hnb hrb).2.2.2
  have hM : PolyT fun x => Mb (beta (n x) (ψ x).length (nbD (n x) (Δ x))) (rbD (beta (n x) (ψ x).length (nbD (n x) (Δ x)))) := by
    unfold Mb
    exact PolyT.sub (PolyT.add hrb.poly hβ.poly) (PolyT.const 1)
  have hfam : PolyT fun x => Fld.famD (ψ x).length (Nat.log 2 (nbD (n x) (Δ x))) := hFam α _ _ hm (log_unary hnb)
  have hX : PolyT fun p : α × List (List ℕ) => evX S (k p.1) (pad p.1) (i p.1) (n p.1) (Δ p.1) (nbD (n p.1) (Δ p.1))
      (Mb (beta (n p.1) (ψ p.1).length (nbD (n p.1) (Δ p.1))) (rbD (beta (n p.1) (ψ p.1).length (nbD (n p.1) (Δ p.1)))))
      (beta (n p.1) (ψ p.1).length (nbD (n p.1) (Δ p.1))) (ψ p.1, p.2) :=
    evX_polyT hEv hP (hk.comp PolyT.id'.fst) (hn.comp PolyT.id'.fst) (hΔ.comp PolyT.id'.fst) (hnb.comp PolyT.id'.fst).poly (PolyT.comp hM PolyT.id'.fst)
      (hβ.comp PolyT.id'.fst) (PolyT.comp hp PolyT.id'.fst) (PolyT.comp hi PolyT.id'.fst) (PolyT.prodMk (PolyT.comp hψ PolyT.id'.fst) PolyT.id'.snd)
  have hsearch := hS α pad (fun x L => evX S (k x) (pad x) (i x) (n x) (Δ x) (nbD (n x) (Δ x))
      (Mb (beta (n x) (ψ x).length (nbD (n x) (Δ x))) (rbD (beta (n x) (ψ x).length (nbD (n x) (Δ x)))))
      (beta (n x) (ψ x).length (nbD (n x) (Δ x))) (ψ x, L)) _ _ _ _ _ _ hp hX hfam hm hnb hβ hrb htb
  simp only [countD]
  exact PolyT.cond' (PolyT.decide_le hm.poly hnb.poly)
    (PolyT.toNat (evF_polyT hEv hP hk hn hΔ hnb.poly hM hp hi (PolyT.prodMk hψ (PolyT.const []))))
    (PolyT.toNat (evF_polyT hEv hP hk hn hΔ hnb.poly hM hp hi (PolyT.prodMk hψ hsearch)))
end VariableBound.Count
