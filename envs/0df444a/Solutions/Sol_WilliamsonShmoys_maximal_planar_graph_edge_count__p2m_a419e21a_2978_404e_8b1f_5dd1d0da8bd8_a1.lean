-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_a419e21a_2978_404e_8b1f_5dd1d0da8bd8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:09:10.002969+00:00
-- url     : https://prove2.me/submissions/86c4034c-2252-4584-83b8-e8048ee07007

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_14be45b2_4af8_4477_b67a_6d2fa4a08c68_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hLcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_14be45b2_4af8_4477_b67a_6d2fa4a08c68_a2
      K hK hcard
  have hnot : ¬ K.edgeSet ⊂ L.edgeSet := fun hproper => hmax L hproper hL
  have hLK : L.edgeSet ⊆ K.edgeSet := by
    intro e he
    by_contra hne
    apply hnot
    exact Set.ssubset_def.mpr ⟨hKL, by
      intro hrev
      exact hne (hrev he)⟩
  have hEq : K.edgeSet = L.edgeSet := Set.Subset.antisymm hKL hLK
  simpa [hEq] using hLcount