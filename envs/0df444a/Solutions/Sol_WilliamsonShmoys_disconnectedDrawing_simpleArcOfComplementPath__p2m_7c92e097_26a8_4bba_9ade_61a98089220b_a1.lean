-- Prove2me | solution 1 for WilliamsonShmoys.disconnectedDrawing_simpleArcOfComplementPath__p2m_7c92e097_26a8_4bba_9ade_61a98089220b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:51:13.556416+00:00
-- url     : https://prove2.me/submissions/f7b1d2bb-d72a-47a5-b3f7-00f6b33dd4f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_simpleArcAvoidingDrawingComplement__p2m_ff2db21c_4994_4086_b5ef_9d99edb0d1bf_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdge : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (u v : V) (huv : u < v) (hnot : ¬ G.Reachable u v)
    (gamma : ℝ → ℝ × ℝ)
    (hcont : ContinuousOn gamma (Set.Icc 0 1))
    (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
    (havoidV : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (havoidE : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x y, x < y → G.Adj x y →
      ∀ s ∈ Set.Icc 0 1, gamma t ≠ arc x y s) :
    ∃ delta : ℝ → ℝ × ℝ,
      ContinuousOn delta (Set.Icc 0 1) ∧
      Set.InjOn delta (Set.Icc 0 1) ∧
      delta 0 = p u ∧ delta 1 = p v ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, delta t ≠ p w) ∧
      (∀ x y, x < y → G.Adj x y →
        ∀ t ∈ Set.Icc 0 1, ∀ s ∈ Set.Icc 0 1,
          delta t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by
  obtain ⟨delta, hdeltaCont, hdeltaInj, hdeltaZero, hdeltaOne,
      hdeltaAvoidV, hdeltaAvoidE⟩ :=
    WilliamsonShmoys.simpleArcAvoidingDrawingComplement__p2m_ff2db21c_4994_4086_b5ef_9d99edb0d1bf_a3
      G p arc u v gamma hcont hzero hone havoidV havoidE
  refine ⟨delta, hdeltaCont, hdeltaInj, hdeltaZero, hdeltaOne,
    hdeltaAvoidV, ?_⟩
  intro x y hxy hAdj t ht s hs hEq
  rcases hEdge x y hxy hAdj with ⟨_, _, _, _, hArcAvoidVertices⟩
  have htEnds : t = 0 ∨ t = 1 := by
    by_contra h
    have htIoo : t ∈ Set.Ioo (0 : ℝ) 1 := by
      rcases Set.mem_Icc.mp ht with ⟨ht0, ht1⟩
      have ht0ne : t ≠ 0 := by
        intro heq
        exact h (Or.inl heq)
      have ht1ne : t ≠ 1 := by
        intro heq
        exact h (Or.inr heq)
      exact ⟨lt_of_le_of_ne ht0 ht0ne.symm, lt_of_le_of_ne ht1 ht1ne⟩
    exact hdeltaAvoidE t htIoo x y hxy hAdj s hs hEq
  have hsEnds : s = 0 ∨ s = 1 := by
    by_contra h
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 := by
      rcases Set.mem_Icc.mp hs with ⟨hs0, hs1⟩
      have hs0ne : s ≠ 0 := by
        intro heq
        exact h (Or.inl heq)
      have hs1ne : s ≠ 1 := by
        intro heq
        exact h (Or.inr heq)
      exact ⟨lt_of_le_of_ne hs0 hs0ne.symm, lt_of_le_of_ne hs1 hs1ne⟩
    rcases htEnds with ht0 | ht1
    · have heq : arc x y s = p u := hEq.symm.trans (by simpa [ht0] using hdeltaZero)
      exact hArcAvoidVertices s hsIoo u heq
    · have heq : arc x y s = p v := hEq.symm.trans (by simpa [ht1] using hdeltaOne)
      exact hArcAvoidVertices s hsIoo v heq
  exact ⟨htEnds, hsEnds⟩