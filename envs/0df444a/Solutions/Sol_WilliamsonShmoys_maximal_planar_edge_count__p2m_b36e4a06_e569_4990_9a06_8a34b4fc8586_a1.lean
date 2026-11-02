-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_b36e4a06_e569_4990_9a06_8a34b4fc8586_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:30:30.553128+00:00
-- url     : https://prove2.me/submissions/be86db7c-2dd8-458d-9375-44fdabc23ffd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_completion__p2m_90a97550_9bbd_4224_be9a_687ae2f63607_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ (M : SimpleGraph V), L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L)
    (hcard : 3 ≤ Fintype.card V)
    (hLdec : DecidableRel L.Adj) :
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI := hLdec
  obtain ⟨M, hMdec, hLM, hM, hMcard⟩ :=
    WilliamsonShmoys.planar_drawing_exact_edge_completion__p2m_90a97550_9bbd_4224_be9a_687ae2f63607_a1
      L hL hcard
  letI := hMdec
  have hML : M ≤ L := hmax M hLM hM
  have hEq : L = M := le_antisymm hLM hML
  cases hEq
  have hDecEq : hMdec = hLdec := by
    funext u v
    exact Subsingleton.elim _ _
  cases hDecEq
  exact hMcard