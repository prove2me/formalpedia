-- Prove2me | solution 1 for SplitSat.reduceCore_decides
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:04:12.639296+00:00
-- url     : https://prove2.me/submissions/ab98825e-043f-4154-9470-2440fd772bc2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SplitSat_Sizes
import Mathlib.Tactic
import Definitions.Def_SplitSat_Walk
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_SatTopK_final_bound
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_const_runs
import Theorems.Thm_Groundwork_Stepped_ite_runs_false
import Theorems.Thm_Groundwork_Stepped_ite_runs_true
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_Stepped_walk_runs
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
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_SplitSat_final_bound
import Theorems.Thm_SplitSat_leaves_stepN
import Theorems.Thm_SplitSat_length_le_of_nodup
import Theorems.Thm_SplitSat_size_node_le
import Theorems.Thm_SplitSat_size_stack_le
import Theorems.Thm_SplitSat_stLeaf
import Theorems.Thm_SplitSat_stack_stepN
import Theorems.Thm_SplitSat_widthP_eq
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
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
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Groundwork.Sparsify WidthK.Prog UniformInK Paper Eight.Width
namespace SplitSat
theorem _root_.solution {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ) {step : Fml → Option (Fml × Fml)} {Dd B Sk : ℕ}
    (hsp : Sparsifies k (δ / 3) step rootP Dd B Sk) (D : StepMachine (List Unit × Fml) Bool) {δ₃ : ℝ} {c : ℕ} (h0 : 0 ≤ δ₃)
    (hδB : δ₃ * (1 + ((k : ℝ) - 3) * B) ≤ δ / 3) (hD : Decides3 D δ₃ c) : ∃ c' : ℕ, DecidesW k (reduceCore step D) δ c' := by
  classical
  obtain ⟨R, hR⟩ : ∃ R, R = 1 + (k - 3) * B := ⟨_, rfl⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, P₀ = 2 ^ k * (2 * k + 1) + 3 := ⟨_, rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P₂, P₂ = (Dd + 1) * (2 ^ k * Sk * (2 * k + 1) + 4) + 1 := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' = cOf P₂ P₀ R c (k + 2) := ⟨_, rfl⟩
  refine ⟨c', fun n ψ hψ hnd => ?_⟩
  obtain ⟨u, hu⟩ : ∃ u : List Unit, u = List.replicate n () := ⟨_, rfl⟩
  obtain ⟨hb1, hb2⟩ := final_bound P₂ P₀ R c (k + 2) (n + 2) (by omega)
  rw [← hc'] at hb1 hb2
  have hm := length_le_of_nodup hψ hnd
  have hc2 : ((c : ℝ) + 2) ≤ (c' : ℝ) := by
    have : c + 2 ≤ c' := by rw [hc']; unfold cOf; omega
    exact_mod_cast this
  have hδn : 0 ≤ δ * (n : ℝ) := by positivity
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * n) := Real.one_le_rpow one_le_two hδn
  have hnilψ : hasNil ψ = true ↔ [] ∈ ψ := by simp [hasNil, List.any_eq_true]
  by_cases hnil : [] ∈ ψ
  · refine ⟨1, false, ?_, ?_, ?_⟩
    · have r := Stepped.ite_runs_true (p := fun p : List Unit × Fml => hasNil p.2)
        (N := Stepped.walk (stepN step) (fun p : List Unit × Fml => ((p.1, rootP p.2) : NFml)) (Stepped.mapIn widthP D))
        (a := (List.replicate n (), ψ)) (hnilψ.2 hnil) (Stepped.const_runs false (List.replicate n (), ψ))
      refine r.mono le_rfl ?_
      have hs := size_node_le hm hψ
      have hp : (n + 2) ^ (k + 1) ≤ (n + 2) ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have hs2 := hs.trans (Nat.mul_le_mul_left _ hp)
      rw [← hP₀] at hs2
      rw [size_bool]
      omega
    · simp only [Bool.false_eq_true, false_iff]
      rintro ⟨a, ha⟩
      obtain ⟨l, hl, -⟩ := ha [] hnil
      simp at hl
    · have : (1 : ℝ) ≤ (c' : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) c]
      push_cast
      nlinarith
  · have hψne : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
      intro C hC
      refine ⟨?_, hψ C hC⟩
      rintro rfl
      exact hnil hC
    obtain ⟨t1, t2, t3, t4⟩ := hsp n ψ hψne
    obtain ⟨L, hL⟩ : ∃ L, L = leaves step (Dd * n) (rootP ψ) := ⟨_, rfl⟩
    rw [← hL] at t1 t2 t3
    have hLN : leaves (stepN step) (Dd * n) ((u, rootP ψ) : NFml) = L.map fun y => ((u, y) : NFml) := by
      rw [hL]; exact leaves_stepN step u _ _
    obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 3 * n) := ⟨_, rfl⟩
    have hE0 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
    have hLE : (L.length : ℝ) ≤ E := by rw [hE]; exact t1
    have hA0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
    have hk' : ∀ y ∈ leaves (stepN step) (Dd * n) ((u, rootP ψ) : NFml), stepN step y = none := by
      rw [hLN]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      simp [stepN, (t2 x hx).1]
    have hT : ∀ y ∈ leaves (stepN step) (Dd * n) ((u, rootP ψ) : NFml),
        (Stepped.mapIn widthP D).Runs y ⌊(c : ℝ) * E⌋₊ (c * (R * (n + 2)) ^ c) (decide (Fml.Sat y.2)) := by
      rw [hLN]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      obtain ⟨-, hxl, hxc⟩ := t2 x hx
      rw [hu]
      obtain ⟨l1, l2, l3, l4⟩ := stLeaf k B n x hxc hxl
      obtain ⟨T, b, r, hb, hTle⟩ := hD _ _ l1 l2
      rw [← widthP_eq] at r
      have e : decide (Fml.Sat x) = b := by
        rw [Bool.eq_iff_iff, decide_eq_true_eq]
        exact (hb.trans l4).symm
      dsimp only
      rw [e]
      refine (Stepped.mapIn_runs r).mono (Nat.le_floor (hTle.trans ?_)) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ c))
      · refine mul_le_mul_of_nonneg_left ?_ hA0
        rw [hE]
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        have l3' : (((widthP (List.replicate n (), x)).1.length : ℕ) : ℝ) ≤ (1 + ((k : ℝ) - 3) * B) * n := by
          have := (Nat.cast_le (α := ℝ)).2 l3
          push_cast [Nat.cast_sub hk] at this
          exact this
        calc δ₃ * ((widthP (List.replicate n (), x)).1.length : ℕ) ≤ δ₃ * ((1 + ((k : ℝ) - 3) * B) * n) := mul_le_mul_of_nonneg_left l3' h0
          _ = δ₃ * (1 + ((k : ℝ) - 3) * B) * n := by ring
          _ ≤ δ / 3 * n := mul_le_mul_of_nonneg_right hδB (Nat.cast_nonneg n)
      · rw [← hR] at l3
        have hR1 : 1 ≤ R := by omega
        have a1 : R * (n + 2) = R * n + 2 * R := by ring
        omega
    have hS : ∀ i, size ((Sparsify.round (stepN step))^[i] ([((u, rootP ψ) : NFml)], [])).1 ≤ P₂ * (n + 2) ^ (k + 2) := by
      intro i
      obtain ⟨s1, s2⟩ := t4 i
      rw [stack_stepN, hu, hP₂]
      refine size_stack_le s1 fun x hx => ⟨(s2 x hx).1.trans ?_, (s2 x hx).2⟩
      calc ψ.length * Sk ≤ 2 ^ k * (n + 2) ^ k * Sk := Nat.mul_le_mul_right _ hm
        _ = 2 ^ k * Sk * (n + 2) ^ k := by ring
    have w := Stepped.walk_runs (stepN step) (root := fun p : List Unit × Fml => ((p.1, rootP p.2) : NFml)) (T := Stepped.mapIn widthP D)
      (Dd * n) (u, ψ) hk' (fun y => decide (Fml.Sat y.2)) ⌊(c : ℝ) * E⌋₊ (c * (R * (n + 2)) ^ c) (P₂ * (n + 2) ^ (k + 2)) hT hS
    rw [hLN] at w
    rw [hu] at w
    refine ⟨(L.map fun y => ((List.replicate n (), y) : NFml)).length * (⌊(c : ℝ) * E⌋₊ + 2), _,
      (Stepped.ite_runs_false (by simpa using fun h => hnil (hnilψ.1 h)) w).mono le_rfl (by omega), ?_, ?_⟩
    · simp only [List.any_map, List.any_eq_true, Function.comp_apply, decide_eq_true_eq]
      constructor
      · rintro ⟨x, hx, a, ha⟩
        exact ⟨a, (t3 fun l => a l.1 = l.2).2 ⟨x, hx, ha⟩⟩
      · rintro ⟨a, ha⟩
        obtain ⟨x, hx, h⟩ := (t3 fun l => a l.1 = l.2).1 ha
        exact ⟨x, hx, a, h⟩
    · have hfl : ((⌊(c : ℝ) * E⌋₊ : ℕ) : ℝ) ≤ (c : ℝ) * E := Nat.floor_le (by positivity)
      have hEE : E * E ≤ (2 : ℝ) ^ (δ * n) := by
        rw [hE, ← Real.rpow_add two_pos]
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        nlinarith
      have hE00 : 0 ≤ E := by linarith
      rw [List.length_map]
      push_cast
      calc (L.length : ℝ) * (((⌊(c : ℝ) * E⌋₊ : ℕ) : ℝ) + 2)
          ≤ E * ((c : ℝ) * E + 2 * E) := mul_le_mul hLE (by linarith) (by positivity) hE00
        _ = ((c : ℝ) + 2) * (E * E) := by ring
        _ ≤ (c' : ℝ) * (2 : ℝ) ^ (δ * n) := mul_le_mul hc2 hEE (by positivity) (Nat.cast_nonneg _)
end SplitSat
