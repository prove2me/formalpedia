-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_ed305078_3eca_42b1_9119_6781033ea8fa_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:28:21.541231+00:00
-- url     : https://prove2.me/submissions/69d39975-2ef7-4e12-ab69-e3c7ac53b1f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_870fe399_b049_44c0_b9a7_7936a0914e85_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hmax : ∀ K : SimpleGraph V,
      J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J)
    (dJ : DecidableRel J.Adj)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel J.Adj := dJ;
      3 * Fintype.card V - 6 ≤ J.edgeFinset.card) := by
  classical
  letI : DecidableRel J.Adj := dJ
  obtain ⟨K, dK, hJK, hKplanar, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_870fe399_b049_44c0_b9a7_7936a0914e85_a2
      J hJ hcard
  letI : DecidableRel K.Adj := dK
  have hKJ : K ≤ J := hmax K hJK hKplanar
  have hgraph : J = K := le_antisymm hJK hKJ
  subst K
  have hd : dK = dJ := by
    funext u v
    exact Subsingleton.elim _ _
  rw [hd] at hcount
  exact le_of_eq hcount