-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_219a8e3b_c7d8_43b3_9ee1_a4b3ebf8e3f2_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:30:11.501982+00:00
-- url     : https://prove2.me/submissions/b07fd2be-d7ef-4434-a6c4-16dca8021271
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_5e572803_fbe6_434b_828d_4b1eaacca01f_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_5e572803_fbe6_434b_828d_4b1eaacca01f_a1
      L hL hV
  have hML : M = L := hMax M hLM hM
  simpa [hML] using hcount