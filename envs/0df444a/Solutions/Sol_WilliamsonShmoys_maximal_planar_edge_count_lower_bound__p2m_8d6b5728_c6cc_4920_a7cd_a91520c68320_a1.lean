-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_8d6b5728_c6cc_4920_a7cd_a91520c68320_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:52:26.963368+00:00
-- url     : https://prove2.me/submissions/7b5e14dd-1e44-48cf-a35b-2604d7de65ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_edge_count__p2m_7d22c919_3efe_4469_8040_ed9baa851075_a1
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K →
      N.edgeFinset ⊆ K.edgeFinset →
      K.edgeFinset ⊆ N.edgeFinset) :
    3 * Fintype.card V - 6 <= N.edgeFinset.card := by
  obtain ⟨K, dK, hK, hNK, hcount⟩ :=
    WilliamsonShmoys.drawable_triangulation_edge_count__p2m_7d22c919_3efe_4469_8040_ed9baa851075_a1
      N dN hN hcard
  have hKN : K.edgeFinset ⊆ N.edgeFinset := hmax K dK hK hNK
  have heq : N.edgeFinset = K.edgeFinset := Finset.Subset.antisymm hNK hKN
  rw [heq, hcount]