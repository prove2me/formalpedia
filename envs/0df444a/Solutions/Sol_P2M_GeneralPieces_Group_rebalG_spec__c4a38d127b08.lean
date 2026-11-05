-- Prove2me | solution 1 for P2M_GeneralPieces_Group_rebalG_spec__c4a38d127b08
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:01:04.87622+00:00
-- url     : https://prove2.me/submissions/94887092-5e72-4374-b9b8-8a918399fa06

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Group_CaseI
import Definitions.Def_GeneralPieces_Group_CaseII
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_CertG
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_GeneralPieces_Group_Lemma
import Theorems.Thm_GeneralPieces_Group_abs_toInst_merge_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_ZW_merged
import Theorems.Thm_Groundwork_Prog_NetE_cap_le
import Theorems.Thm_Groundwork_Prog_NetE_lbLen_eq
import Theorems.Thm_Groundwork_Prog_NetE_length_members
import Theorems.Thm_Groundwork_Prog_NetE_stLen_le
import Theorems.Thm_Groundwork_Prog_NetE_toInst_eq_mergedVal
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
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
import Theorems.Thm_PaddedDescent_Col_goodG_iff
import Theorems.Thm_PaddedDescent_F_RebalF_cap_le
import Theorems.Thm_PaddedDescent_F_RebalF_mergedF_eq
import Theorems.Thm_PaddedDescent_F_RebalF_mergedP_eq
import Theorems.Thm_PaddedDescent_F_RebalF_stLen_le
import Theorems.Thm_PaddedDescent_F_Table_stT1
import Theorems.Thm_PaddedDescent_F_Table_stT2
import Theorems.Thm_PaddedDescent_F_Table_stT3a
import Theorems.Thm_PaddedDescent_F_rng_eq
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
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
open GeneralPieces GeneralPieces.Group
open Finset Groundwork
variable {J J' σ τ A : Type*}
open Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F PaddedDescent.F.RebalF PaddedDescent.Col
namespace GeneralPieces.Group
theorem _root_.solution {C : Type} (pad : U) (K g β : ℕ) (F : FNet C) (c : C) (N : Network (Fin g) (List Bool) (List Bool)) (P B : ℕ)
    (hK : 2 ≤ K) (hg0 : 0 < g) (hβ1 : 1 ≤ β) (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B)
    (hex : ∃ x < K ^ g, goodG K g F.toP β (c, x) = true)
    (f1 : K ^ g ≤ pad.length) (f2 : 2 ^ (P * (2 * g / K)) ≤ pad.length) (f3 : 2 ^ P ≤ pad.length)
    (f4 : 2 ^ ((K - 1) * β) ≤ pad.length) :
    ∃ J, rebalG pad K g β F c = some J ∧ zval K J = N.value ∧ J.1.length = β ∧ WF K β (P * (2 * g / K) + B * g ^ 2) J := by
  have hK0 : 0 < K := by omega
  obtain ⟨x', hx', hgood'⟩ := hex
  obtain ⟨x, hfind⟩ : ∃ x, (List.range (K ^ g)).find? (fun x => goodG K g F.toP β (c, x)) = some x := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨x', List.mem_range.2 hx', hgood'⟩
  have hgood : goodG K g F.toP β (c, x) = true := List.find?_some (p := fun x => goodG K g F.toP β (c, x)) hfind
  obtain ⟨hg1, hg2⟩ := (goodG_iff F.toP hK0 hN β x).1 hgood
  obtain ⟨m, hmdef⟩ : ∃ m, m = 2 * g / K := ⟨_, rfl⟩
  rw [← hmdef] at f2 ⊢
  have hm : ∀ G, #{a : Fin g | chi hK0 x a = G} ≤ m := fun G => by
    rw [hmdef, Nat.le_div_iff_mul_le hK0, Nat.mul_comm]
    exact (hg1 G).le
  have hm' : ∀ G < K, (members K g x G).length ≤ m := fun G hG => by
    rw [length_members hK0 x ⟨G, hG⟩]; exact hm _
  have hβ' : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g F.toP c x G G' ≤ β := fun G hG G' hG' hne => by
    have hne' : (⟨G, hG⟩ : Fin K) ≠ ⟨G', hG'⟩ := fun e => hne (congrArg Fin.val e)
    rw [lbLen_eq F.toP hK0 hN x hne']
    exact hg2 _ _ hne'
  have hentry : ∀ (G : Fin K) (θ : Fin K → List Bool), WFQ β G θ →
      mergedF pad K g F ((c, x), (G.1, List.ofFn θ)) =
        (N.merge (chi hK0 x) [] []).toInst (mD K g F.toP c x β) (mdec K g F.toP c x) G θ := by
    rintro G θ ⟨hθ, hG⟩
    rw [toInst_eq_mergedVal F.toP hK0 hN x β G θ hθ, ← mergedP_eq hN hS x β m hm' hβ' G θ hθ hG]
    refine mergedF_eq ?_ fun y i hi hW => ?_
    · exact (Nat.pow_le_pow_right (by norm_num) (PaddedDescent.F.RebalF.stLen_le hN hS (hm' G G.2))).trans f2
    · have ha : i / g < g := Nat.div_lt_of_lt_mul hi
      have hb : i % g < g := Nat.mod_lt _ hg0
      have hab : (⟨i / g, ha⟩ : Fin g) ≠ ⟨i % g, hb⟩ := by
        intro e
        have e' : i / g = i % g := congrArg Fin.val e
        simp [isW, e'] at hW
      exact (Nat.pow_le_pow_right (by norm_num) (PaddedDescent.F.RebalF.cap_le hN hS hab)).trans f3
  have habs : ∀ (G : Fin K) (θ : Fin K → List Bool), WFQ β G θ →
      (mergedF pad K g F ((c, x), (G.1, List.ofFn θ))).natAbs ≤ 2 ^ (P * m + B * g ^ 2) := by
    intro G θ hq
    rw [hentry G θ hq]
    have h : |(N.merge (chi hK0 x) [] []).toInst (mD K g F.toP c x β) (mdec K g F.toP c x) G θ| ≤ 2 ^ (P * m + B * g ^ 2) := by
      simpa only [Fintype.card_fin] using abs_toInst_merge_le N (chi hK0 x) [] [] _ _ hS hm G θ
    rw [Int.abs_eq_natAbs] at h
    exact_mod_cast h
  refine ⟨(List.replicate β (), tabulate pad K β fun q => mergedF pad K g F ((c, x), q)), ?_, ?_, by simp, ?_⟩
  · unfold rebalG
    rw [rng_eq f1, hfind]
    rfl
  · unfold zval
    simp only [List.length_replicate]
    rw [Table.stT1 K β _ ((N.merge (chi hK0 x) [] []).toInst (mD K g F.toP c x β) (mdec K g F.toP c x))
      fun G θ hq => by rw [instOf, Table.stT2 pad K β _ f4 G θ hq, hentry G θ hq]]
    exact ZW_merged F.toP hK0 hN x β fun G G' hlt => by
      rw [lbLen_eq F.toP hK0 hN x hlt.ne]; exact hg2 _ _ hlt.ne
  · exact Table.stT3a pad K β β _ _ f4 hβ1 le_rfl habs
end GeneralPieces.Group
