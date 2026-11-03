-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_34ce151f_05d3_497c_a88f_b630e2f0d090_a1__p2m_34ce151f_05d3_497c_a88f_b630e2f0d090_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:58:18.976863+00:00
-- url     : https://prove2.me/submissions/1c1daa03-76fa-4505-9091-0e51851a30b7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_9948da09_8892_4f55_9a10_a3a5f578a96b_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V) :
    Exists fun L : SimpleGraph V => K <= L /\ HasPlanarDrawingOn L /\
      (letI : DecidableRel L.Adj := Classical.decRel _;
       L.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_9948da09_8892_4f55_9a10_a3a5f578a96b_a1 K hK hn
  refine ⟨L, hKL, hL, ?_⟩
  simpa only [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] using hcount