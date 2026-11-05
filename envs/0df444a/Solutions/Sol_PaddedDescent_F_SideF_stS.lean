-- Prove2me | solution 1 for PaddedDescent.F.SideF.stS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:39:47.698634+00:00
-- url     : https://prove2.me/submissions/8bae7f08-4a8b-46bb-8a4d-f37fbae70aac

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_F_Price
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_PaddedDescent_F_SideF
import Theorems.Thm_PaddedDescent_F_SideF_itemF_eq
import Theorems.Thm_Groundwork_Grid_node_lt
import Theorems.Thm_Groundwork_Grid_sideN_c
import Theorems.Thm_Groundwork_Grid_sideN_lab
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_map_range_eq_ofFn
import Theorems.Thm_Groundwork_Prog_presents
import Theorems.Thm_Groundwork_Prog_sideN_W_eq
import Theorems.Thm_Groundwork_Prog_sideN_f_eq
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
import Theorems.Thm_PaddedDescent_F_RebalF_presents
import Theorems.Thm_PaddedDescent_F_prodL_eq
attribute [local fun_prop] Groundwork.PolyT.length
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.SideF
open Groundwork Groundwork.Prog Groundwork.Grid Finset
namespace PaddedDescent.F.SideF
theorem _root_.solution : StS := by
  intro pad gU tr ℓU y T h
  refine RebalF.presents sideF _ _ (fun a => rfl) (fun a b hab => sideN_c _ _ _ _ _ hab)
    (fun a b hab => sideN_lab _ _ _ _ _ hab) (fun a z hz => ?_) (fun a b z θ hab hz hθ => ?_)
  · change sideWF gU.length tr ℓU.length y T (a.val, z) = _
    rw [sideN_W_eq (lam := fun n : ℕ => n) (instOf (K := gU.length * gU.length) T) ℓU.length y a hz]
    unfold sideWF sideWv
    cases sideChk gU.length tr (fun n : ℕ => n) ((ℓU.length, y), (a.val, z)) with
    | false => simp
    | true =>
      simp only [cond_true, if_true, prodL_eq]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [dif_pos (node_lt tr a.2 (Finset.mem_range.1 hi)), instOf, map_range_eq_ofFn]
  · change sideFF pad gU.length tr ℓU.length y ((a.val, b.val), (z, θ)) = _
    rw [sideN_f_eq (lam := fun n : ℕ => n) (instOf (K := gU.length * gU.length) T) ℓU.length y hab hz hθ]
    unfold sideFF sideFv
    cases sideEdges gU.length tr (fun n : ℕ => n) ((ℓU.length, y), ((a.val, b.val), (z, θ))) with
    | false => simp
    | true =>
      simp only [cond_true, if_true, prodL_eq, itemF_eq _ _ _ _ _ _ _ _ _ h]
end PaddedDescent.F.SideF
