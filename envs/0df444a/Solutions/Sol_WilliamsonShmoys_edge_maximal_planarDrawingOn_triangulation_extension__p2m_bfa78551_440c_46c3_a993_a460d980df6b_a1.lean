-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planarDrawingOn_triangulation_extension__p2m_bfa78551_440c_46c3_a993_a460d980df6b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:07:50.748182+00:00
-- url     : https://prove2.me/submissions/cbb24898-91b9-4570-8d72-1c5fd45ea140
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanarExtension__p2m_e8d3fd6d_990f_43df_873b_df1b4f477345_a2
import Theorems.Thm_WilliamsonShmoys_maximalPlanarDrawingOn_edgeCount__p2m_e8d3fd6d_990f_43df_873b_df1b4f477345_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : HasPlanarDrawingOn H)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      HasPlanarDrawingOn K ∧
      (letI : DecidableRel H.Adj := dH
       letI : DecidableRel K.Adj := dK
       H.edgeFinset ⊆ K.edgeFinset ∧
       K.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨K, dK, hK, hHK, hmax⟩ :=
    WilliamsonShmoys.edgeMaximalPlanarExtension__p2m_e8d3fd6d_990f_43df_873b_df1b4f477345_a2
      H dH hH
  have hcount :=
    WilliamsonShmoys.maximalPlanarDrawingOn_edgeCount__p2m_e8d3fd6d_990f_43df_873b_df1b4f477345_a2
      K dK hK hn hmax
  refine ⟨K, dK, hK, ?_⟩
  letI : DecidableRel H.Adj := dH
  letI : DecidableRel K.Adj := dK
  exact ⟨hHK, hcount⟩