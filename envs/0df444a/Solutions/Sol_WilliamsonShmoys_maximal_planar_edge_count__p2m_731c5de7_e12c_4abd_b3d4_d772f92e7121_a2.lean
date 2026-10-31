-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_731c5de7_e12c_4abd_b3d4_d772f92e7121_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:16:38.461995+00:00
-- url     : https://prove2.me/submissions/c3925263-264f-431f-b901-3829735d6c78

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_1bca9e8d_9b62_4fe4_94af_9f67da983417_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet →
      HasPlanarDrawingOn N → Set.Subset N.edgeSet M.edgeSet) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_1bca9e8d_9b62_4fe4_94af_9f67da983417_a1
      M hM hCard
  have hNM : Set.Subset N.edgeSet M.edgeSet := hmax N hMN hN
  have heq : M.edgeSet = N.edgeSet := Set.Subset.antisymm hMN hNM
  rw [heq]
  exact hCount