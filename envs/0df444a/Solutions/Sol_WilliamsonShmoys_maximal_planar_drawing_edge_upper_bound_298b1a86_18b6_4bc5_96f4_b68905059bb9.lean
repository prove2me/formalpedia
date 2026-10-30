-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound_298b1a86_18b6_4bc5_96f4_b68905059bb9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:55:38.908062+00:00
-- url     : https://prove2.me/submissions/4d3f96cf-e7c7-4215-816e-c5dbff786dca

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_completion_v3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_v3
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_of_adj_imp_v3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V) :
    N.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  classical
  obtain ⟨M, hsub, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_completion_v3 N hNdraw
  have hmono : N.edgeSet.ncard <= M.edgeSet.ncard :=
    WilliamsonShmoys.edgeSet_ncard_mono_of_adj_imp_v3 N M hsub
  have hcount : M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_v3 M hmax hCard
  omega
