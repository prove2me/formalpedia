-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_878f63d5_f8a4_40b9_aba3_29559d5a92e2_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:49:12.545821+00:00
-- url     : https://prove2.me/submissions/f9e15b24-1a13-456b-a21e-e155119598f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_completion_exact_edge_count__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1
import Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeSet_ncard_mono__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1
import Mathlib
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  have hConn := WilliamsonShmoys.maximal_planar_graph_connected__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1 M hM hV hMax
  obtain ⟨H, hMH, hHdraw, hHcount⟩ := WilliamsonShmoys.connected_planar_completion_exact_edge_count__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1 M hM hV hConn
  have hHM : H ≤ M := hMax H hMH hHdraw
  have hcount : H.edgeSet.ncard ≤ M.edgeSet.ncard :=
    WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1 H M hHM
  calc
    3 * Fintype.card V - 6 = H.edgeSet.ncard := hHcount
    _ ≤ M.edgeSet.ncard := hcount