-- Prove2me | solution 1 for Value.prod_groupTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:39:10.185897+00:00
-- url     : https://prove2.me/submissions/7e4e43f1-4314-4886-9220-fbc13d891ad3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Blocks
import Definitions.Def_Value_Sums
import Definitions.Def_Value_Joint
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_congr
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
import Theorems.Thm_Value_prod_across
import Theorems.Thm_Value_prod_inside
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
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}
namespace Value
theorem _root_.solution (N : Net g) (χ : Fin g → Fin K) (z : Fin g → List Bool) (θ : Fin g × Fin g → List Bool) :
    ∏ γ, groupTerm N χ θ γ (fun a => if χ a = γ then z a else []) = jointTerm N χ z θ := by
  have h0 : ∀ γ, groupTerm N χ θ γ (fun a => if χ a = γ then z a else []) = groupTerm N χ θ γ z := by
    intro γ
    unfold groupTerm
    congr 1
    · congr 1
      · refine prod_congr rfl fun a ha => ?_
        simp only [if_pos (mem_filter.1 ha).2]
      · refine prod_congr rfl fun p hp => ?_
        simp only [if_pos (mem_filter.1 hp).2.1, if_pos (mem_filter.1 hp).2.2]
    · refine prod_congr rfl fun p hp => ?_
      simp only [if_pos (mem_filter.1 hp).2.1]
  simp only [h0]
  unfold groupTerm jointTerm
  rw [prod_mul_distrib, prod_mul_distrib, Finset.prod_fiberwise univ χ fun a => N.W a (z a), prod_inside χ fun p => N.Ψ p.1 p.2 (z p.1) (z p.2),
    prod_across χ fun p => N.f p.1 p.2 (z p.1) (θ (pr p.1 p.2))]
  congr 1
  refine prod_congr rfl fun p hp => ?_
  have hlt : p.1 < p.2 := (mem_filter.1 (mem_filter.1 hp).1).2
  simp only [Prod.fst_swap, Prod.snd_swap, (pr_of_lt hlt).1, (pr_of_lt hlt).2]
end Value
