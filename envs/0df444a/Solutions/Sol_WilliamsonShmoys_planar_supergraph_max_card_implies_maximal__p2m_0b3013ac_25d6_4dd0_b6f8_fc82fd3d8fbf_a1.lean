-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_max_card_implies_maximal__p2m_0b3013ac_25d6_4dd0_b6f8_fc82fd3d8fbf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:00:43.745434+00:00
-- url     : https://prove2.me/submissions/b1fbf876-531f-4794-b767-f5139b9b37e1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hsub : G.edgeFinset ⊆ K.edgeFinset)
    (hmax : ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn L →
      G.edgeFinset ⊆ L.edgeFinset →
      L.edgeFinset.card ≤ K.edgeFinset.card) :
    ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeFinset ⊆ L.edgeFinset →
      K.edgeFinset = L.edgeFinset := by
  intro L dL hL hKL
  have hGL : G.edgeFinset ⊆ L.edgeFinset := hsub.trans hKL
  have hcard : L.edgeFinset.card ≤ K.edgeFinset.card := hmax L dL hL hGL
  exact Finset.eq_of_subset_of_card_le hKL hcard