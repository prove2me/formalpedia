-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_maximal_supergraph__p2m_db367b77_db98_427b_b1c6_513aa1e72eeb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:18:12.953229+00:00
-- url     : https://prove2.me/submissions/93027c9a-81de-425a-af77-e9010977cb5d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hDraw : HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V, N ≤ P ∧ HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q ≤ P := by
  classical
  let S : Set (SimpleGraph V) := {P | N ≤ P ∧ HasPlanarDrawingOn P}
  have hFinite : S.Finite := Set.toFinite S
  have hN : N ∈ S := ⟨le_rfl, hDraw⟩
  obtain ⟨P, hNP, hMax⟩ := hFinite.exists_le_maximal hN
  have hPS : P ∈ S := hMax.prop
  refine ⟨P, hNP, hPS.2, ?_⟩
  intro Q hPQ hQDraw
  by_contra hQP
  have hne : P ≠ Q := by
    intro heq
    apply hQP
    rw [heq]
  have hlt : P < Q := lt_of_le_of_ne hPQ hne
  exact hMax.not_prop_of_gt hlt ⟨hNP.trans hPQ, hQDraw⟩