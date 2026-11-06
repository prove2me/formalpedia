-- Prove2me | solution 1 for Suffices.stLoopRunsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:55:55.763197+00:00
-- url     : https://prove2.me/submissions/006f81fe-f9a3-4ddb-acc9-0ad28eb738fb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Sizes
import Definitions.Def_Exits_Runs
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_Suffices_Loop
import Theorems.Thm_Suffices_isKCNF_toN
import Theorems.Thm_Suffices_le_length_enc
import Theorems.Thm_CountKSat_stDecU
import Theorems.Thm_Groundwork_Decode_length_toN
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_ite_runs_false
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_Stepped_mapOut_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
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
import Theorems.Thm_Groundwork_Unary_const
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
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_Suffices_loop_bound
import Theorems.Thm_Suffices_size_node_le
import Theorems.Thm_Suffices_size_stack_le
import Theorems.Thm_Suffices_tested_map
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.const
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
open Suffices
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits
open Groundwork.Sparsify (leaves)
namespace Suffices
theorem _root_.solution : StLoopRunsOf := by
  intro HW ε M τ hE
  refine ⟨143 * (UniformInK.bsumU τ 3 + 1) + 5, fun Mc n φ h3 hnil v t Sm hMc => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, N = (Sat3.enc φ).length + 1 := ⟨_, rfl⟩
  obtain ⟨hn, hm⟩ := le_length_enc φ
  rw [← hN] at hn hm ⊢
  have h1 : 1 ≤ N := by omega
  have hk := isKCNF_toN h3 hnil
  have hdec : decU 3 (Sat3.enc φ) = (List.replicate n (), Decode.toN φ) := stDecU 3 n φ (by norm_num) h3.1
  have hψl : (Decode.toN φ).length ≤ N := by rw [Decode.length_toN]; exact hm
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Fml, ψ = Decode.toN φ := ⟨_, rfl⟩
  rw [← hψ] at hMc hk hdec hψl ⊢
  have hnilψ : hasNil ψ = false := by
    rw [hasNil, List.any_eq_false]
    intro C hC
    simpa using (hk C hC).1
  -- the formulas tested are the outputs of the leaves tested
  have el : (tested (fun x => posZ (v (SparsificationLemma.out x))) (leaves (rule τ) (depth τ n) (rootC (List.replicate n (), ψ)))).length = (tested (fun Φ => posZ (v Φ)) (produced τ n ψ)).length := by
    unfold produced start
    rw [tested_map, List.length_map]
  have ea : (leaves (rule τ) (depth τ n) (rootC (List.replicate n (), ψ))).any (fun x => posZ (v (SparsificationLemma.out x))) = (produced τ n ψ).any fun Φ => posZ (v Φ) :=
    (List.any_map (f := SparsificationLemma.out) (p := fun Φ => posZ (v Φ))).symm
  have hT : ∀ x ∈ tested (fun x => posZ (v (SparsificationLemma.out x))) (leaves (rule τ) (depth τ n) (rootC (List.replicate n (), ψ))),
      (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut Mc posZ)).Runs x t Sm (posZ (v (SparsificationLemma.out x))) := by
    intro x hx
    refine Stepped.mapIn_runs (Stepped.mapOut_runs (hMc (SparsificationLemma.out x) ?_))
    unfold produced start
    rw [tested_map]
    exact List.mem_map_of_mem hx
  -- the stack
  have hS : ∀ i, size ((Sparsify.round (rule τ))^[i] ([rootC (List.replicate n (), ψ)], [])).1 ≤ (143 * (UniformInK.bsumU τ 3 + 1) + 1) * N ^ 3 := by
    intro i
    obtain ⟨s1, s2⟩ := hE.stack n ψ hk i
    exact size_stack_le s1 (fun x hx => size_node_le (s2 x hx).1 (s2 x hx).2.1 (s2 x hx).2.2.1 (s2 x hx).2.2.2 hψl hn h1) hn h1
  have w := HW (List Unit × Fml) CNode (rule τ) rootC (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut Mc posZ)) (depth τ n) (List.replicate n (), ψ) (hE.stops n ψ hk)
    (fun x => posZ (v (SparsificationLemma.out x))) t Sm ((143 * (UniformInK.bsumU τ 3 + 1) + 1) * N ^ 3) hT hS
  rw [el, ea] at w
  have r := Stepped.ite_runs_false (p := fun p : List Unit × Fml => hasNil p.2) (M := Stepped.const false) (a := (List.replicate n (), ψ)) hnilψ w
  rw [← hdec] at r
  have hb := loop_bound (UniformInK.bsumU τ 3) N h1
  exact (Stepped.mapIn_runs r).mono (by omega) (by omega)
end Suffices
