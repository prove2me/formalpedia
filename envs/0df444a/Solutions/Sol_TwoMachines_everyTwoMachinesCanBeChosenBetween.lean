-- Prove2me | solution 1 for TwoMachines.everyTwoMachinesCanBeChosenBetween
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:11:35.864205+00:00
-- url     : https://prove2.me/submissions/da5d28c9-3b48-40cc-81ae-69e6b6e93e27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_TwoMachines_Defs
import Definitions.Def_Wrap_CodingExists
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_TwoMachines_Main
import Theorems.Thm_P2M_TwoMachines_exists_bound__28fef89684c0
import Theorems.Thm_TwoMachines_exists_length_le
import Theorems.Thm_CountKSat_exists_tmW
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_branch_runs_inl
import Theorems.Thm_Groundwork_Stepped_branch_runs_inr
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
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
import Theorems.Thm_Wrap_Outputs_mono
import Theorems.Thm_Wrap_coding_exists
import Theorems.Thm_Wrap_sim_runs
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
open TwoMachines
open Turing Groundwork Wrap CircuitLowerBound.Tab
variable {M₁ M₂ : TM2ComputableAux Bool Bool}
namespace TwoMachines
theorem _root_.solution : EveryTwoMachinesCanBeChosenBetween := by
  intro M₁ M₂ hf₁ hf₂ test pre₁ pre₂ post₁ post₂ htest hpre₁ hpre₂ hpost₁ hpost₂
  obtain ⟨K₁⟩ := coding_exists M₁ hf₁
  obtain ⟨K₂⟩ := coding_exists M₂ hf₂
  have i₁ := sim_isPolyT K₁ hpre₁ hpost₁
  have i₂ := sim_isPolyT K₂ hpre₂ hpost₂
  have : IsPolyT (choose K₁ K₂ test pre₁ pre₂ post₁ post₂) := IsPolyT.ite htest
  obtain ⟨N, q₀, hfin, hN⟩ := CountKSat.exists_tmW (choose K₁ K₂ test pre₁ pre₂ post₁ post₂)
  obtain ⟨c₁, hc₁⟩ := exists_length_le hpre₁
  obtain ⟨c₂, hc₂⟩ := exists_length_le hpre₂
  obtain ⟨q₁, hq₁⟩ := exists_bound₂ q₀ K₁.a 1 c₁ 0
  obtain ⟨q₂, hq₂⟩ := exists_bound₂ q₀ K₂.a 1 c₂ 0
  refine ⟨K₁, K₂, N, q₀, max q₁ q₂, hfin, hN, fun x y t => ⟨fun ht h => ?_, fun ht h => ?_⟩⟩
  · have hr : (choose K₁ K₂ test pre₁ pre₂ post₁ post₂).Runs x t (K₁.a * ((pre₁ x).length + 1) + K₁.a * t + 1) (post₁ y) :=
      Stepped.branch_runs_inl (by simp [Stepped.iteSel, ht]) (sim_runs K₁ pre₁ post₁ h)
    refine Outputs.mono (hN x _ _ _ hr) (le_trans ?_ ((hq₁ t x.length _ 0 (hc₁ x) (Nat.zero_le _)).trans ?_))
    · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) q₀)
    · exact Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  · have hr : (choose K₁ K₂ test pre₁ pre₂ post₁ post₂).Runs x t (K₂.a * ((pre₂ x).length + 1) + K₂.a * t + 1) (post₂ y) :=
      Stepped.branch_runs_inr (by simp [Stepped.iteSel, ht]) (sim_runs K₂ pre₂ post₂ h)
    refine Outputs.mono (hN x _ _ _ hr) (le_trans ?_ ((hq₂ t x.length _ 0 (hc₂ x) (Nat.zero_le _)).trans ?_))
    · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) q₀)
    · exact Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
end TwoMachines
