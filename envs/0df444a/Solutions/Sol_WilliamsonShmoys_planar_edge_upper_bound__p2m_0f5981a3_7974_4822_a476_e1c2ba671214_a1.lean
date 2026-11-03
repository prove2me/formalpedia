-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_0f5981a3_7974_4822_a476_e1c2ba671214_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:21:03.09013+00:00
-- url     : https://prove2.me/submissions/d083ddf0-fc2c-4723-88ed-2485bf596d54

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a1__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a1__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hP : HasPlanarDrawingOn P) :
    P.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  have hext :=
    WilliamsonShmoys.maximal_planar_extension__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a1__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a2
      P hP
  let H : SimpleGraph V := Classical.choose hext
  have hprops := Classical.choose_spec hext
  have hPH : P <= H := hprops.1
  have hH : HasPlanarDrawingOn H := hprops.2.1
  have hmax :
      forall K : SimpleGraph V, H <= K -> HasPlanarDrawingOn K -> K = H :=
    hprops.2.2
  have hle : P.edgeSet.ncard <= H.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hPH)
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a1__p2m_63f4596f_16e9_46f5_8d7e_b4c7e853b2c9_a2
      H hcard hH hmax
  omega
