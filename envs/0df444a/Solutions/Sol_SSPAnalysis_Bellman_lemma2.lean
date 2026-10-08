-- Prove2me | solution 1 for SSPAnalysis.Bellman.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:56:25.234724+00:00
-- url     : https://prove2.me/submissions/3e115f18-40d2-46d0-9f9b-2ff21b2fcb27

import Mathlib
import Definitions.Def_SSPAnalysis_Bellman_SSP

set_option autoImplicit false

namespace SSPAnalysis.Bellman.L2Aux

open SSPAnalysis.Bellman

theorem term_le {n : ℕ} {U : Fin n → Type*} (m : Model n U) (x y : Fin n → ℝ)
    (i : Fin n) (u : U i) :
    m.c i u + ∑ j, m.p i u j * x j ≤ (m.c i u + ∑ j, m.p i u j * y j) + dist x y := by
  have h : ∑ j, m.p i u j * x j ≤ ∑ j, m.p i u j * y j + ∑ j, m.p i u j * dist x y := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have hj : x j - y j ≤ dist x y := by
      have := dist_le_pi_dist x y j
      rw [Real.dist_eq] at this
      exact le_trans (le_abs_self _) this
    have hp := m.p_nonneg i u j
    nlinarith
  rw [← Finset.sum_mul, m.p_sum_one i u, one_mul] at h
  linarith

theorem coord_le {n : ℕ} {U : Fin n → Type*} (m : Model n U) (hT : m.TRealValued)
    (x y : Fin n → ℝ) (i : Fin n) : m.T x i ≤ m.T y i + dist x y := by
  obtain ⟨hne, hbx⟩ := hT x i
  have : m.T x i - dist x y ≤ m.T y i := by
    unfold Model.T
    apply le_ciInf
    intro u
    have h1 : (⨅ u : U i, (m.c i u + ∑ j, m.p i u j * x j)) ≤ m.c i u + ∑ j, m.p i u j * x j :=
      ciInf_le hbx u
    have h2 := term_le m x y i u
    linarith
  linarith

end SSPAnalysis.Bellman.L2Aux

open Topology SSPAnalysis.Bellman in
theorem solution {n : ℕ} [NeZero n] {U : Fin n → Type*}
    (m : Model n U) (h1 : m.Assumption1)
    (hT : m.TRealValued) :
    ContinuousOn m.T (X n) := by
  have hL : LipschitzWith 1 m.T := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    rw [dist_pi_le_iff dist_nonneg]
    intro i
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor
    · linarith [SSPAnalysis.Bellman.L2Aux.coord_le m hT x y i]
    · linarith [SSPAnalysis.Bellman.L2Aux.coord_le m hT y x i, dist_comm x y]
  exact hL.continuous.continuousOn
