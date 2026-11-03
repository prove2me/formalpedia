-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_upper_bound__p2m_8b804cdd_68ca_48da_bde7_dd4a5c81f51a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:24:12.072706+00:00
-- url     : https://prove2.me/submissions/5f278204-bcf1-4003-9f6a-9ed52a19eb14

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    N.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_upper_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513 N hcard hplanar