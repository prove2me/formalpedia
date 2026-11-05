-- Prove2me | solution 1 for PaddedDescent.inRateTM_of_algorithm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:54:04.161938+00:00
-- url     : https://prove2.me/submissions/96e7ce7f-7e84-4257-9365-10747bc2ac37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_PadRate
import Definitions.Def_PaddedDescent_BrutePad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_PaddedDescent_Reduce
import Theorems.Thm_PaddedDescent_eOf_polyT
import Theorems.Thm_PaddedDescent_eOf_enc
import Theorems.Thm_PaddedDescent_le_padLog
import Theorems.Thm_PaddedDescent_withBrute_polyT
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
import Theorems.Thm_PaddedDescent_bruteA_enc_of_le
import Theorems.Thm_PaddedDescent_inRateTM_of_padded
import Theorems.Thm_PaddedDescent_nOf_enc
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
open PaddedDescent
open Groundwork Groundwork.Decode Sat3 Turing
namespace PaddedDescent
theorem _root_.solution (C₀ s₀ : ℕ) (hC : 2 ^ s₀ ≤ C₀) {A : List Bool × List Unit → Bool} (hA : PolyT A)
    (h : ∀ (n : ℕ) (φ : CNF n), Is3CNF φ → s₀ ≤ sOf n → (A (enc φ, pad (padLog C₀ n)) = true ↔ Satisfiable φ)) :
    InRateTM (3 / 19) := by
  refine inRateTM_of_padded (eOf_polyT C₀) (withBrute_polyT s₀ hA) C₀ fun n φ h3 => ?_
  rw [eOf_enc C₀ h3]
  refine ⟨le_rfl, ?_⟩
  by_cases hs : sOf n < s₀
  · have e1 : withBrute s₀ A (enc φ, pad (padLog C₀ n)) = bruteA (enc φ, pad (padLog C₀ n)) := by
      simp [withBrute, nOf_enc h3, hs]
    rw [e1]
    refine bruteA_enc_of_le h3 ?_
    have h4 : 2 ^ sOf n ≤ C₀ := (Nat.pow_le_pow_right (by norm_num) hs.le).trans hC
    simpa [pad] using Nat.pow_le_pow_right (by norm_num : 0 < 2) (le_padLog h4)
  · have e1 : withBrute s₀ A (enc φ, pad (padLog C₀ n)) = A (enc φ, pad (padLog C₀ n)) := by
      simp [withBrute, nOf_enc h3, hs]
    rw [e1]
    exact h n φ h3 (not_lt.1 hs)
end PaddedDescent
