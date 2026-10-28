-- Prove2me | solution 1 for WilliamsonShmoys.drawable_completion_from_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:47:54.166867+00:00
-- url     : https://prove2.me/submissions/d07e11c9-6e8c-47ad-904a-3701296fd178

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hBound : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet.ncard ≤ 3 * Fintype.card V - 6)
    (hAug : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet.ncard < 3 * Fintype.card V - 6 →
      ∃ N : SimpleGraph V,
        M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        N.edgeSet.ncard = M.edgeSet.ncard + 1) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 = M.edgeSet.ncard := by
  classical
  let K : Nat := 3 * Fintype.card V - 6
  have hLBound : L.edgeSet.ncard ≤ K := by
    exact hBound L hL
  have aux : ∀ d : Nat, ∀ M : SimpleGraph V,
      M.edgeSet.ncard ≤ K → K - M.edgeSet.ncard = d →
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
      ∃ P : SimpleGraph V,
        L ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
        P.edgeSet.ncard = K := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro M hMc hgap hLM hM
        by_cases heq : M.edgeSet.ncard = K
        · exact ⟨M, hLM, hM, heq⟩
        · have hlt : M.edgeSet.ncard < K := by omega
          obtain ⟨N, hMN, hN, hNcount⟩ := hAug M hLM hM hlt
          have hNc : N.edgeSet.ncard ≤ K := hBound N hN
          have hdec : K - N.edgeSet.ncard < d := by omega
          have hLN : L ≤ N := le_trans hLM hMN
          exact ih (K - N.edgeSet.ncard) hdec N hNc rfl hLN hN
  obtain ⟨M, hLM, hM, hMcount⟩ :=
    aux (K - L.edgeSet.ncard) L hLBound rfl le_rfl hL
  refine ⟨M, hLM, hM, ?_⟩
  simpa [K] using hMcount.symm