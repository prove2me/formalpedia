-- Prove2me | solution 1 for ThinFlowSP.Breakpoints.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:59:55.409827+00:00
-- url     : https://prove2.me/submissions/dc20f35b-9d3a-4a8d-8864-13ff352f0201

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Network

open ThinFlowSP.Breakpoints in
theorem solution (G : Net) (hloop : ∀ a, G.tail a ≠ G.head a) (ν : G.A → ℝ)
    (hν : ∀ a, 0 < ν a) :
    laplacian G ν = incidence G * Matrix.diagonal ν * (incPos G).transpose := by
  ext v w
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  have hpos : ∀ a, incPos G w a = if G.head a = w then 1 else 0 := by
    intro a
    have hl := hloop a
    simp only [incPos, incidence, Matrix.of_apply]
    split_ifs with h1 h2 h2
    · exact absurd (h2.trans h1.symm) hl
    · norm_num
    · norm_num
    · norm_num
  simp_rw [hpos]
  simp only [laplacian, incidence, Matrix.of_apply]
  by_cases hvw : v = w
  · subst hvw
    rw [if_pos rfl, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hl := hloop a
    generalize G.tail a = x at hl ⊢
    generalize G.head a = y at hl ⊢
    split_ifs <;> subst_vars <;> first | exact (hl rfl).elim | ring1
  · rw [if_neg hvw, Finset.sum_filter, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hl := hloop a
    rw [ite_and]
    generalize G.tail a = x at hl ⊢
    generalize G.head a = y at hl ⊢
    split_ifs <;> subst_vars <;> first | exact (hl rfl).elim | exact (hvw rfl).elim | ring1
