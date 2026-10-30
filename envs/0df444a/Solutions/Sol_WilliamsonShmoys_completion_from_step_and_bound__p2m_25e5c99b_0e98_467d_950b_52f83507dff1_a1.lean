-- Prove2me | solution 1 for WilliamsonShmoys.completion_from_step_and_bound__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:37:51.244484+00:00
-- url     : https://prove2.me/submissions/cf88fc5a-ca91-4c6f-bece-0a33db950d1a

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hbound : ∀ G, P G → 3 ≤ Fintype.card V →
      G.edgeSet.ncard ≤ 3 * Fintype.card V - 6)
    (hstep : ∀ G, P G → 3 ≤ Fintype.card V →
      G.edgeSet.ncard < 3 * Fintype.card V - 6 →
      ∃ K : SimpleGraph V,
        G ≤ K ∧ P K ∧ K.edgeSet.ncard = G.edgeSet.ncard + 1)
    (H : SimpleGraph V)
    (hH : P H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧ K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  let B : Nat := 3 * Fintype.card V - 6
  have iterate : ∀ n : Nat, ∀ G : SimpleGraph V, P G →
      G.edgeSet.ncard ≤ B → B - G.edgeSet.ncard = n →
      ∃ K : SimpleGraph V, G ≤ K ∧ P K ∧ K.edgeSet.ncard = B := by
    intro n
    induction n with
    | zero =>
        intro G hG hle hdiff
        refine ⟨G, le_rfl, hG, ?_⟩
        omega
    | succ n ih =>
        intro G hG hle hdiff
        have hlt : G.edgeSet.ncard < B := by omega
        obtain ⟨K, hGK, hK, hKcard⟩ := hstep G hG hV (by simpa [B] using hlt)
        have hKle : K.edgeSet.ncard ≤ B := by
          simpa [B] using hbound K hK hV
        obtain ⟨L, hKL, hL, hLcard⟩ := ih K hK hKle (by omega)
        refine ⟨L, le_trans hGK hKL, hL, hLcard⟩
  have hHle : H.edgeSet.ncard ≤ B := by
    simpa [B] using hbound H hH hV
  obtain ⟨K, hHK, hK, hKcard⟩ := iterate (B - H.edgeSet.ncard) H hH hHle rfl
  exact ⟨K, hHK, hK, by simpa [B] using hKcard⟩