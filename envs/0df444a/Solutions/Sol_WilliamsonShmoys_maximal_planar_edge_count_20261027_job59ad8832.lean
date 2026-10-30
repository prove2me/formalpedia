-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_20261027_job59ad8832
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:23:09.515118+00:00
-- url     : https://prove2.me/submissions/2de11d69-be1a-4ed7-a379-de4e0554ab07

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_tight_edge_count_20261028_job9e56ac28

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hKmax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨L, hsub, hLplanar, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_tight_edge_count_20261028_job9e56ac28
      K hV hKplanar
  have hnotproper : ¬ K.edgeSet ⊂ L.edgeSet := by
    intro hproper
    exact hKmax L hproper hLplanar
  have heq : K.edgeSet = L.edgeSet :=
    Set.Subset.antisymm hsub (by
      intro e he
      by_contra hne
      apply hnotproper
      refine ⟨hsub, ?_⟩
      intro h
      exact hne (h he))
  simpa [heq] using hcount
