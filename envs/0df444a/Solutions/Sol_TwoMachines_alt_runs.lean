-- Prove2me | solution 1 for TwoMachines.alt_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:10:58.09321+00:00
-- url     : https://prove2.me/submissions/0d5c7729-c885-4d7e-add1-67fc80fdaf48

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
import Theorems.Thm_TwoMachines_alt_out_running
import Theorems.Thm_TwoMachines_alt_step_rep
import Theorems.Thm_TwoMachines_alt_init
import Theorems.Thm_TwoMachines_exists_halt
import Theorems.Thm_TwoMachines_eq_of_halted
import Theorems.Thm_TwoMachines_out_haltList
import Theorems.Thm_TwoMachines_size_rep_le
import Theorems.Thm_CircuitLowerBound_Tab_Enc_step
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
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
theorem _root_.solution (K₁ : Coding M₁) (K₂ : Coding M₂) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) {x y₁ y₂ : List Bool} {t₁ t₂ : ℕ}
    (h₁ : Outputs M₁ (pre₁ x) y₁ t₁) (h₂ : Outputs M₂ (pre₂ x) y₂ t₂) (he : post₁ y₁ = post₂ y₂) :
    (alt K₁ K₂ pre₁ pre₂ post₁ post₂).Runs x (min t₁ t₂)
      (K₁.a * ((pre₁ x).length + 1) + K₁.a * min t₁ t₂ + (K₂.a * ((pre₂ x).length + 1) + K₂.a * min t₁ t₂)) (post₁ y₁) := by
  classical
  obtain ⟨n₁, hn₁, e₁⟩ := exists_halt h₁
  obtain ⟨n₂, hn₂, e₂⟩ := exists_halt h₂
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = start M₁ (pre₁ x) := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c, c = start M₂ (pre₂ x) := ⟨_, rfl⟩
  rw [← hc₁] at e₁
  rw [← hc₂] at e₂
  have hex : ∃ j, ((stay M₁)^[j] c₁).l = none ∨ ((stay M₂)^[j] c₂).l = none := ⟨n₁, Or.inl (by rw [e₁]; rfl)⟩
  obtain ⟨h, hh⟩ : ∃ h, h = Nat.find hex := ⟨_, rfl⟩
  have hspec : ((stay M₁)^[h] c₁).l = none ∨ ((stay M₂)^[h] c₂).l = none := hh ▸ Nat.find_spec hex
  have hmin : ∀ i < h, ((stay M₁)^[i] c₁).l ≠ none ∧ ((stay M₂)^[i] c₂).l ≠ none := fun i hi => by
    have := Nat.find_min hex (hh ▸ hi)
    exact not_or.1 this
  have hh₁ : h ≤ n₁ := hh ▸ Nat.find_min' hex (Or.inl (by rw [e₁]; rfl))
  have hh₂ : h ≤ n₂ := hh ▸ Nat.find_min' hex (Or.inr (by rw [e₂]; rfl))
  have hht : h ≤ min t₁ t₂ := le_min (hh₁.trans hn₁) (hh₂.trans hn₂)
  obtain ⟨S, hS⟩ : ∃ S, S = K₁.a * ((pre₁ x).length + 1) + K₁.a * min t₁ t₂ + (K₂.a * ((pre₂ x).length + 1) + K₂.a * min t₁ t₂) := ⟨_, rfl⟩
  rw [← hS]
  have hsize : ∀ i ≤ h, size ((K₁.rep ((stay M₁)^[i] c₁), K₂.rep ((stay M₂)^[i] c₂)) : Rep × Rep) ≤ S := fun i hi => by
    have a₁ := size_rep_le K₁ (pre₁ x) (hi.trans hht)
    have a₂ := size_rep_le K₂ (pre₂ x) (hi.trans hht)
    rw [← hc₁] at a₁
    rw [← hc₂] at a₂
    rw [hS]
    exact Nat.add_le_add a₁ a₂
  have hout : (alt K₁ K₂ pre₁ pre₂ post₁ post₂).out (K₁.rep ((stay M₁)^[h] c₁), K₂.rep ((stay M₂)^[h] c₂)) = some (post₁ y₁) := by
    by_cases g₁ : ((stay M₁)^[h] c₁).l = none
    · rw [eq_of_halted g₁ hh₁ e₁]
      simp only [alt, out_haltList]
    · have g₂ : ((stay M₂)^[h] c₂).l = none := hspec.resolve_left g₁
      rw [eq_of_halted g₂ hh₂ e₂]
      simp only [alt, K₁.out_running _ g₁, out_haltList, Option.map_some, he]
  have key : ∀ d i, i + d = h → (alt K₁ K₂ pre₁ pre₂ post₁ post₂).Reaches S (post₁ y₁) (K₁.rep ((stay M₁)^[i] c₁), K₂.rep ((stay M₂)^[i] c₂)) d := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have : i = h := by omega
      subst this
      exact .halt hout (hsize _ le_rfl)
    | succ d ih =>
      intro i hi
      obtain ⟨g₁, g₂⟩ := hmin i (by omega)
      refine .step (alt_out_running K₁ K₂ pre₁ pre₂ post₁ post₂ g₁ g₂) (hsize i (by omega)) ?_
      rw [alt_step_rep, ← Function.iterate_succ_apply' (stay M₁), ← Function.iterate_succ_apply' (stay M₂)]
      exact ih (i + 1) (by omega)
  have hr : (alt K₁ K₂ pre₁ pre₂ post₁ post₂).Runs x h S (post₁ y₁) := by
    unfold Stepped.Runs
    rw [alt_init, ← hc₁, ← hc₂]
    exact key h 0 (by omega)
  exact hr.mono hht le_rfl
end TwoMachines
