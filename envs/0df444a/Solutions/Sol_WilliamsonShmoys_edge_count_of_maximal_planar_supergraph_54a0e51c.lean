-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_supergraph_54a0e51c
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:25:21.304216+00:00
-- url     : https://prove2.me/submissions/66bc23ec-1334-425c-90e3-d52a162e4b76

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_54a0e51c
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_54a0e51c

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L M : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hLM : L.edgeSet ⊆ M.edgeSet)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      L.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ M.edgeSet) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_edge_count_upper_bound_54a0e51c M hV hM
  · by_contra hnot
    have hlt : M.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
    obtain ⟨N, hpair⟩ :=
      WilliamsonShmoys.planar_edge_augmentation_54a0e51c M hV hM hlt
    have hMN : M.edgeSet ⊆ N.edgeSet := hpair.1
    have hNMnot : ¬ N.edgeSet ⊆ M.edgeSet := hpair.2.1
    have hN : WilliamsonShmoys.HasPlanarDrawingOn N := hpair.2.2
    have hNM : N.edgeSet ⊆ M.edgeSet := hmax N (hLM.trans hMN) hN
    exact hNMnot hNM