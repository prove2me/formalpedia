-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:59:18.519784+00:00
-- url     : https://prove2.me/submissions/2a5e66fa-9b71-49af-9891-f5336cf5c311

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph__p2m_b69f5d0b_8d80_4770_82d5_e0533af83150_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ J : SimpleGraph V, H <= J → HasPlanarDrawingOn J → J <= H) :
    3 * Fintype.card V - 6 <= H.edgeSet.ncard := by
  obtain ⟨J, hHJ, hJ, hcount⟩ :=
    WilliamsonShmoys.exists_triangulated_planar_supergraph__p2m_b69f5d0b_8d80_4770_82d5_e0533af83150_a1
      H hH hV
  have hJH : J <= H := hmax J hHJ hJ
  have hEq : J = H := le_antisymm hJH hHJ
  rw [← hEq]
  omega

