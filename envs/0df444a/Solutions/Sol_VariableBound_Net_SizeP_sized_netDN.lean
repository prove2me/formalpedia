-- Prove2me | solution 1 for VariableBound.Net.SizeP.sized_netDN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:51:45.035059+00:00
-- url     : https://prove2.me/submissions/c169e321-52af-4722-ab9d-5ac0c1ee823b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Net_SizeB
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Net_SizeP
import Theorems.Thm_VariableBound_Net_SizeP_sum_capD_le
import Theorems.Thm_VariableBound_Net_SizeP_abs_boole_le
import Theorems.Thm_VariableBound_Net_SizeP_one_le_two_pow
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Count_abs_boole_le
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
import Theorems.Thm_Groundwork_card_words
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
import Theorems.Thm_VariableBound_Net_Tests_capD_comm
import Theorems.Thm_VariableBound_Net_Tests_length_rep
import Theorems.Thm_VariableBound_Net_Tests_sum_erase_fin
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
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}
namespace VariableBound.Net.SizeP
theorem _root_.solution {P B y : ℕ} {fl : Bool} (h1 : ∀ a < g, qv g n + (tch g n D a).length ≤ P) (h2 : ∀ a < g, 2 * (tch g n D a).length ≤ P)
    (h3 : ∀ a < g, ∀ z, |WD g n D y fl a z| ≤ 2 ^ B) : (netDN g (ctx g n D y fl)).Sized P B where
  card_S a := by
    simp only [netDN, netD, ctx, Tests.length_rep, card_words]
    exact Nat.pow_le_pow_right (by norm_num) (h1 a a.2)
  c_symm a b := by
    simp only [netDN, netD, ctx, Tests.length_rep]
    exact Tests.capD_comm _ _ _
  sum_c a := by
    simp only [netDN, netD, ctx, Tests.length_rep]
    rw [Tests.sum_erase_fin a fun b => capD g n D y a.val b]
    exact (sum_capD_le y a.2).trans (h2 a a.2)
  card_lab a b _ := by
    simp only [Network.lab, netDN, netD, ctx, Tests.length_rep, card_words]
    refine Nat.pow_le_pow_right (by norm_num) (le_of_eq ?_)
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab, max_eq_right hab]
    · rw [min_eq_right hab, max_eq_left hab, Tests.capD_comm]
  abs_W a z := by
    simp only [netDN, netD, ctx, Tests.length_rep]
    exact h3 a a.2 z
  abs_f a b z θ := by
    simp only [netDN, netD]
    exact (abs_boole_le _).trans (one_le_two_pow B)
  abs_Ψ a b z z' _ := by
    simp only [Network.Ψ, netDN, netD]
    refine le_trans ?_ (one_le_two_pow B)
    have e : ∀ (L L' θ : List Bool), ((if (L == θ) = true then (1 : ℤ) else 0) * if (L' == θ) = true then 1 else 0) =
        if θ = L ∧ θ = L' then 1 else 0 := by
      intro L L' θ
      by_cases h1 : θ = L
      · by_cases h2 : θ = L'
        · subst h1; simp [← h2]
        · have h2' : ¬ L' = θ := fun h => h2 h.symm
          simp [h2, h2']
      · have h1' : ¬ L = θ := fun h => h1 h.symm
        simp [h1, h1']
    simp only [e]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, abs_of_nonneg (Nat.cast_nonneg _)]
    refine Nat.cast_le_one.2 (card_le_one.2 fun θ hθ θ' hθ' => ?_)
    exact ((mem_filter.1 hθ).2.1).trans ((mem_filter.1 hθ').2.1).symm
end VariableBound.Net.SizeP
