-- Prove2me | solution 1 for SparsifyThenCount.stCorrectDG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:36:41.679011+00:00
-- url     : https://prove2.me/submissions/4aa9570d-7bc6-47e7-a728-8ec59b16b5d9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_VariableBound_Top_Correct
import Definitions.Def_VariableBound_Top_Correct
import Definitions.Def_SparsifyThenCount_Correct
import Theorems.Thm_CountKSatRate_Leaf_spec
import Theorems.Thm_CountKSat_CountTop_outW_eq
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
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
import Theorems.Thm_UniformInK_Correct_brute_eq
import Theorems.Thm_UniformInK_Correct_kcU_eq
import Theorems.Thm_VariableBound_Correct_planAtD_some
attribute [local fun_prop] Groundwork.PolyT.all
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
open SparsifyThenCount
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.Correct VariableBound VariableBound.Correct VariableBound.Net
open PaddedDescent.F.Mark (WfL occ nSat)
namespace SparsifyThenCount
theorem _root_.solution (hC : StCountD) (hB : StBudgetD) (hR : StRoundsDG) (hWC : StepSparsify.StWalkCountG) (hD : StDecM) (hBr : StBruteC) (hDU : StDecU) : StCorrectDG := by
  intro Θ Lc hSv Idx _ S e C₀ Q hS slU k n φ hk h3 pad hpad
  obtain ⟨hdk, hdec⟩ := hD k n φ hk h3.1
  have hkU : kU (SatM.enc k φ) = k := by rw [kU, hdk, List.length_replicate]
  have hn : nU (SatM.enc k φ) = n := by rw [nU, hdec, List.length_replicate]
  obtain ⟨i, hi⟩ : ∃ i, i = idxU Q.pick (SatM.enc k φ) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = precU Q.pick slU (SatM.enc k φ) := ⟨_, rfl⟩
  have hplan : planD S Q.pick slU (SatM.enc k φ) = planAtD S k n i s := by rw [planD, hkU, hn, hi, hs]
  have hnum : (bif (planD S Q.pick slU (SatM.enc k φ)).isNone then bruteU (SatM.enc k φ, pad)
      else numDG Θ S (kcU (kU (SatM.enc k φ)) (nU (SatM.enc k φ))) (idxU Q.pick (SatM.enc k φ)) (precU Q.pick slU (SatM.enc k φ)) (fmlOf (SatM.enc k φ)) pad) = SatK.numSat φ := by
    rw [eD, hplan, hn] at hpad
    rw [hplan, ← hi, ← hs, hkU, hn, hdec]
    cases hpl : planAtD S k n i s with
    | none =>
      rw [hpl, Option.getD_none] at hpad
      simp only [Option.isNone_none, cond_true, bruteU, hdec, List.length_replicate]
      exact brute_eq hBr hDU φ hk h3 pad hpad
    | some v =>
      rw [hpl, Option.getD_some] at hpad
      obtain ⟨⟨c1, c2, c3⟩, c6⟩ := planAtD_some hS hpl
      have hblock : blockU k n s = 2 ^ betaU k s := min_eq_left c2
      obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = blockU k n s := ⟨_, rfl⟩
      rw [← hblock, ← hΔ] at c3
      rw [c6, needD, pow_add, ← hΔ] at hpad
      have hp1 : 2 ^ needNet S i (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) (BbD k n) ≤ pad.length :=
        le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hpad
      have hp2 : 2 ^ restD k (S.K i) n s ≤ pad.length := le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) hpad
      obtain ⟨b1, b2, -, b4⟩ := hB k (S.K i) n s pad.length hk c1 hp2
      have b3 := hR k (S.K i) n s pad.length hp2
      rw [← hΔ] at b1 b2
      have q1 : Lc k s + 2 ≤ Δ := by rw [hΔ, hblock]; exact hSv.par k s hk c1
      have hΔ2 : 2 ≤ Δ := by omega
      have hoki : ∃ l, i = Q.idx l := ⟨_, hi.trans (Q.pick_idx _)⟩
      have hK2 : 2 ≤ S.K i := by obtain ⟨l, rfl⟩ := hoki; exact Q.K_two l
      simp only [Option.isNone_some, cond_false, numDG, kcU_eq c2, List.length_replicate]
      refine hWC Θ Lc hSv k s n φ pad _ hk h3 c1 b3 b4 fun x hxl hx1 ho hs' => ?_
      obtain ⟨m1, m2, m3, m4⟩ := Leaf.spec hk hx1 ho hs'
      have hlen : (leafM x).length ≤ Δ * n := (m1.trans hxl).trans (Nat.mul_le_mul_right _ q1)
      unfold valD
      rw [← hΔ, hC Idx S (fun i => ∃ l, i = Q.idx l) Q.correct k pad i n Δ (leafM x) hoki hK2 m2 (fun v => (m3 v).trans q1) hlen hΔ2 c3 ⟨hp1, b1, b2⟩, m4]
  unfold ADG
  dsimp only
  rw [hnum, hdec]
  exact CountTop.outW_eq _ _ _
end SparsifyThenCount
