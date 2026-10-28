-- Prove2me | solution 1 for WilliamsonShmoys.triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_maximal_edge_count_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:23:37.583649+00:00
-- url     : https://prove2.me/submissions/724ded42-8b4e-44d7-8bc8-97da7ecc872c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_completion_task_2f486b23_4a17_4b27_89f1_8ee712518760
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_task_2f486b23_4a17_4b27_89f1_8ee712518760

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  classical
  let hcomp := WilliamsonShmoys.maximal_planar_supergraph_completion_task_2f486b23_4a17_4b27_89f1_8ee712518760 K hV hK
  let L := Classical.choose hcomp
  have hspec := Classical.choose_spec hcomp
  have hKL := hspec.1
  have hL := hspec.2.1
  have hLmax := hspec.2.2
  have hLK : L = K := hmax L hKL hL
  rw [hLK.symm]
  exact WilliamsonShmoys.maximal_planar_edge_lower_bound_task_2f486b23_4a17_4b27_89f1_8ee712518760 L hV hL hLmax