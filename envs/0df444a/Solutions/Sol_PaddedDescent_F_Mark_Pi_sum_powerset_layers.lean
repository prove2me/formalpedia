-- Prove2me | solution 1 for PaddedDescent.F.Mark.Pi.sum_powerset_layers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:13:29.5424+00:00
-- url     : https://prove2.me/submissions/ee993fe9-b397-4361-a1e0-abb7542ddc61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkPi
import Theorems.Thm_PaddedDescent_F_Mark_Pi_sum_powerset_union
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_filter
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
attribute [local fun_prop] Groundwork.PolyT.filter
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Pi
open Finset Groundwork Groundwork.Prog
variable {ι : Type*} [DecidableEq ι]
namespace PaddedDescent.F.Mark.Pi
theorem _root_.solution (lay : ι → ℕ) (φ : ℕ → Finset ι → ℤ) (R : ℕ) (V : Finset ι) (hV : ∀ e ∈ V, lay e < R) :
    ∑ X ∈ V.powerset, ∏ i ∈ range R, φ i (X.filter fun e => lay e = i) =
      ∏ i ∈ range R, ∑ P ∈ (V.filter fun e => lay e = i).powerset, φ i P := by
  induction R generalizing V with
  | zero =>
    have : V = ∅ := eq_empty_of_forall_notMem fun e he => absurd (hV e he) (Nat.not_lt_zero _)
    subst this
    simp
  | succ R ih =>
    have hsplit : V = (V.filter fun e => lay e < R) ∪ V.filter fun e => lay e = R := by
      ext e
      simp only [mem_union, mem_filter]
      constructor
      · intro he
        have := hV e he
        rcases Nat.lt_succ_iff_lt_or_eq.1 this with h | h
        · exact Or.inl ⟨he, h⟩
        · exact Or.inr ⟨he, h⟩
      · rintro (h | h) <;> exact h.1
    have hdis : Disjoint (V.filter fun e => lay e < R) (V.filter fun e => lay e = R) := by
      rw [disjoint_left]
      intro e h1 h2
      have := (mem_filter.1 h1).2
      have := (mem_filter.1 h2).2
      omega
    have key := sum_powerset_union hdis (fun P => ∏ i ∈ range R, φ i (P.filter fun e => lay e = i)) (φ R)
    rw [← hsplit, ih _ fun e he => (mem_filter.1 he).2] at key
    rw [prod_range_succ, ← prod_congr rfl (g := fun i => ∑ P ∈ (V.filter fun e => lay e = i).powerset, φ i P) ?_] 
    · rw [← key]
      refine sum_congr rfl fun X hX => ?_
      have hX := mem_powerset.1 hX
      rw [prod_range_succ]
      congr 1
      · refine prod_congr rfl fun i hi => ?_
        congr 1
        ext e
        simp only [mem_filter, mem_inter]
        constructor
        · rintro ⟨he, rfl⟩; exact ⟨⟨he, hX he, mem_range.1 hi⟩, rfl⟩
        · rintro ⟨⟨he, -⟩, h⟩; exact ⟨he, h⟩
      · congr 1
        ext e
        simp only [mem_filter, mem_inter]
        constructor
        · rintro ⟨he, h⟩; exact ⟨he, hX he, h⟩
        · rintro ⟨he, -, h⟩; exact ⟨he, h⟩
    · intro i hi
      congr 2
      ext e
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨he, -⟩, h⟩; exact ⟨he, h⟩
      · rintro ⟨he, rfl⟩; exact ⟨⟨he, mem_range.1 hi⟩, rfl⟩
end PaddedDescent.F.Mark.Pi
