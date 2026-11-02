-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_4cd8dc85_f1ac_41e1_bc75_323e85ca2348_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:03:13.798216+00:00
-- url     : https://prove2.me/submissions/94ce1bb6-4dc2-419e-b0ca-36e52eb52d7c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b36e4a06_e569_4990_9a06_8a34b4fc8586_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_b36e4a06_e569_4990_9a06_8a34b4fc8586_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (L : SimpleGraph V), K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ (hLdec : DecidableRel L.Adj),
        L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hLdraw, hLmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_b36e4a06_e569_4990_9a06_8a34b4fc8586_a1
      K hK
  refine ⟨L, hKL, hLdraw, ?_⟩
  intro hLdec
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_b36e4a06_e569_4990_9a06_8a34b4fc8586_a1
    L hLdraw hLmax hcard hLdec