-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_completion__p2m_b8cc851b_d85e_44da_b799_273002cb7d7c_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T05:54:53.693982+00:00
-- url     : https://prove2.me/submissions/3bf3361d-aee4-4557-bcfd-f651cc344452
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_f34871aa_4b26_4166_99f3_d88e1cde8300_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_f34871aa_4b26_4166_99f3_d88e1cde8300_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      N <= K ∧ HasPlanarDrawingOn K ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨K, hNK, hK, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_f34871aa_4b26_4166_99f3_d88e1cde8300_a2
      N hN
  have hEdges :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_f34871aa_4b26_4166_99f3_d88e1cde8300_a2
      K hK hCard hMax
  exact ⟨K, hNK, hK, hEdges⟩