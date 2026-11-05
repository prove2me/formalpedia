-- Prove2me | solution 1 for PaddedDescent.F.Table.stT2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:12:13.832905+00:00
-- url     : https://prove2.me/submissions/a7561276-9274-4b85-a999-796f0751029a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_PaddedDescent_F_Table
import Theorems.Thm_PaddedDescent_F_Table_block_flatten
import Theorems.Thm_PaddedDescent_F_Table_flatten_skip
import Theorems.Thm_Groundwork_Decode_block_flatten
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
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_ofWord_lt
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
import Theorems.Thm_Groundwork_toWord_ofWord
import Theorems.Thm_PaddedDescent_F_rng_eq
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Table
open Groundwork Groundwork.Prog Finset
namespace PaddedDescent.F.Table
theorem _root_.solution : StT2 := by
  intro pad K ℓ F h v θ hq
  obtain ⟨hθ, hv⟩ := hq
  obtain ⟨t, ht⟩ : ∃ t : ℕ → List Bool, t = fun u => (List.ofFn θ).getD u [] := ⟨_, rfl⟩
  have htθ : ∀ u : Fin K, t u.1 = θ u := fun u => by rw [ht]; simp [u.2]
  have hof : List.ofFn θ = (List.range K).map t := by
    refine List.ext_getElem (by simp) fun u h1 h2 => ?_
    have hu : u < K := by simpa using h1
    simp [ht, hu]
  obtain ⟨L, hL⟩ : ∃ L, L = (List.range (K - 1)).map fun j => t (skip v.1 j) := ⟨_, rfl⟩
  have hskip : ∀ j, j < K - 1 → skip v.1 j < K ∧ skip v.1 j ≠ v.1 := by
    intro j hj; unfold skip; split_ifs <;> omega
  have hLlen : ∀ w ∈ L, w.length = ℓ := by
    intro w hw
    rw [hL] at hw
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hw
    obtain ⟨h1, h2⟩ := hskip j (List.mem_range.1 hj)
    rw [htθ ⟨_, h1⟩]
    exact hθ _ fun e => h2 (congrArg Fin.val e)
  have hfl : (List.ofFn θ).flatten = L.flatten := by
    rw [hof, hL]; exact flatten_skip t K v.1 v.2 (by rw [htθ v]; exact hv)
  have hLl : L.length = K - 1 := by rw [hL]; simp
  have hwl : L.flatten.length = (K - 1) * ℓ := by
    rw [List.length_flatten, List.map_congr_left (g := fun _ => ℓ) hLlen, List.map_const', List.sum_replicate, hLl,
      smul_eq_mul]
  have hlt : ofWord (List.ofFn θ).flatten < 2 ^ ((K - 1) * ℓ) := by rw [hfl, ← hwl]; exact ofWord_lt _
  have hun : unflat K ℓ v.1 (toWord ((K - 1) * ℓ) (ofWord (List.ofFn θ).flatten)) = List.ofFn θ := by
    rw [hfl, ← hwl, toWord_ofWord, hof]
    unfold unflat
    refine List.map_congr_left fun u hu => ?_
    have huK : u < K := List.mem_range.1 hu
    split_ifs with h1 h2
    · rw [h1, htθ v, hv]
    · rw [block_flatten L u hLlen (by omega), hL]
      have : u < K - 1 := by omega
      simp [List.getD_eq_getElem?_getD, this, skip, h2]
    · have h3 : u - 1 < K - 1 := by omega
      rw [block_flatten L (u - 1) hLlen (by omega), hL]
      have h4 : ¬ u - 1 < v.1 := by omega
      have h5 : u - 1 + 1 = u := by omega
      simp [List.getD_eq_getElem?_getD, h3, skip, h4, h5]
  unfold look tabulate
  have hrow : ((List.range K).map fun v' => (rng pad (2 ^ ((K - 1) * ℓ))).map fun i =>
      F (v', unflat K ℓ v' (toWord ((K - 1) * ℓ) i))).getD v.1 [] =
      (rng pad (2 ^ ((K - 1) * ℓ))).map fun i => F (v.1, unflat K ℓ v.1 (toWord ((K - 1) * ℓ) i)) := by
    simp [List.getD_eq_getElem?_getD, v.2]
  simp only [hrow]
  rw [rng_eq h]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt, Option.map_some, Option.getD_some]
  rw [hun]
end PaddedDescent.F.Table
