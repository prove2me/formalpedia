-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_extension_triangulated__p2m_b8ffaa04_868a_495a_ab39_10d09a3d9b95_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:55:12.817049+00:00
-- url     : https://prove2.me/submissions/b09b049a-9efe-4798-9d68-2e523c970f4a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_drawable_extension__p2m_6e736750_a362_4363_844e_e38c08b33ed2_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_inclusion_maximal_drawable__p2m_6e736750_a362_4363_844e_e38c08b33ed2_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (_hKdec : DecidableRel K.Adj),
      M ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hKdec, hMK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_drawable_extension__p2m_6e736750_a362_4363_844e_e38c08b33ed2_a1
      M hM
  letI : DecidableRel K.Adj := hKdec
  have hcount :=
    WilliamsonShmoys.edge_count_of_inclusion_maximal_drawable__p2m_6e736750_a362_4363_844e_e38c08b33ed2_a1
      K hKplanar hcard hKmax
  exact ⟨K, hKdec, hMK, hKplanar, hcount⟩