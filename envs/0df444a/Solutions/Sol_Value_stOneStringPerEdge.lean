-- Prove2me | solution 1 for Value.stOneStringPerEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:46:40.065209+00:00
-- url     : https://prove2.me/submissions/e1c40b44-23ea-4e8b-be4b-524135548a27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_Value_Clique
import Theorems.Thm_Eight_SecNetworks_length_copyAt
import Theorems.Thm_Eight_SecNetworks_star_mem
import Theorems.Thm_Eight_SecNetworks_sum_settings
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
import Theorems.Thm_Groundwork_mem_tuples
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_pr_of_lt
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
import Theorems.Thm_Value_existsUnique_of_sum
import Theorems.Thm_Value_existsUnique_pi
import Theorems.Thm_Value_existsUnique_tuple
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
open Value
open Groundwork Groundwork.Prog Finset Eight.SecNetworks
namespace Value
theorem _root_.solution : StOneStringPerEdge := by
  intro K lam
  constructor
  · intro Λ hΛ
    refine (existsUnique_congr fun z => ?_).2 (existsUnique_pi (fun (w : Fin K) (zw : List Bool) => zw ∈ words ((K - 1) * lam) ∧ ∀ w' : Fin K, w' ≠ w → copyAt lam w w' zw = star Λ w w') fun w => ?_)
    · rw [Fintype.mem_piFinset]
      exact forall_and.symm
    · have H := existsUnique_of_sum (words ((K - 1) * lam)) (tuples (fun w' => w' ≠ w) (fun _ => words lam) []) (fun z (w' : Fin K) => if w' = w then [] else copyAt lam w w' z)
        (sum_settings lam w) (fun t' => ∀ w' : Fin K, w' ≠ w → t' w' = star Λ w w')
        (existsUnique_tuple _ _ _ (star Λ w) fun w' hw' => ((mem_tuples _ _ _ _).1 (star_mem hΛ w) w').1 hw')
      refine (existsUnique_congr fun zw => and_congr_right fun _ => forall_congr' fun w' => imp_congr_right fun hw' => ?_).1 H
      simp only [if_neg hw']
  · intro z hz hag
    rw [Fintype.mem_piFinset] at hz
    refine ⟨fun p => if p.1 < p.2 then copyAt lam p.1 p.2 (z p.1) else [], (mem_tuples _ _ _ _).2 fun p => ⟨fun hp => ?_, fun hp => if_neg hp⟩, fun w w' hne => ?_⟩
    · rw [if_pos hp, mem_words]
      exact length_copyAt p.1 p.2 hp.ne' (mem_words.1 (hz p.1))
    · rcases lt_or_gt_of_ne hne with h | h
      · change _ = (fun p : Fin K × Fin K => if p.1 < p.2 then copyAt lam p.1 p.2 (z p.1) else []) (pr w w')
        rw [(pr_of_lt h).2]
        exact ((if_pos h).trans (hag (w', w) (mem_filter.2 ⟨mem_univ _, h⟩))).symm
      · change _ = (fun p : Fin K × Fin K => if p.1 < p.2 then copyAt lam p.1 p.2 (z p.1) else []) (pr w w')
        rw [(pr_of_lt h).1]
        exact (if_pos h).symm
end Value
