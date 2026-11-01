-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_5de819de_a434_4eee_9d51_0646a941be0a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:51:28.323805+00:00
-- url     : https://prove2.me/submissions/d34f6a51-931f-4200-8d55-ee5d36f71249
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph__p2m_24d4a109_2712_447f_b6c6_168aeb4ef393_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K →
      H.edgeFinset ⊆ K.edgeFinset →
      K.edgeFinset ⊆ H.edgeFinset) :
    H.edgeFinset.card + 6 = 3 * Fintype.card V := by
  obtain ⟨K, dK, hK, hsub, hcardK⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_24d4a109_2712_447f_b6c6_168aeb4ef393_a1
      H dH hH hcard
  have hrev : K.edgeFinset ⊆ H.edgeFinset := hmax K dK hK hsub
  have heq : H.edgeFinset = K.edgeFinset := Finset.Subset.antisymm hsub hrev
  have hcardeq : H.edgeFinset.card = K.edgeFinset.card := congrArg Finset.card heq
  omega