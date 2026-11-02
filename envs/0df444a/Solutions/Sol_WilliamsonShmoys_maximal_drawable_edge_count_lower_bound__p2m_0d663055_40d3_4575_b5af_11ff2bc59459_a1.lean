-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_0d663055_40d3_4575_b5af_11ff2bc59459_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:58:12.520129+00:00
-- url     : https://prove2.me/submissions/7126f33a-a994-43bc-96e4-4d1bf17ee2f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph__p2m_4cd8dc85_f1ac_41e1_bc75_323e85ca2348_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) (_hLdec : DecidableRel L.Adj),
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by
  classical
  obtain ⟨L, hKL, hLplanar, hLcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_4cd8dc85_f1ac_41e1_bc75_323e85ca2348_a4 K hK hcard
  have hLK : L ≤ K := hmax L (Classical.decRel L.Adj) hKL hLplanar
  have hEq : L = K := le_antisymm hLK hKL
  subst L
  have hCountK := hLcount (inferInstance : DecidableRel K.Adj)
  exact hCountK.symm.le