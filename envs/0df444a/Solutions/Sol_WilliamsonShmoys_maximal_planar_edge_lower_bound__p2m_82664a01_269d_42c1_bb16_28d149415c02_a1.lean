-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_82664a01_269d_42c1_bb16_28d149415c02_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:09:15.066057+00:00
-- url     : https://prove2.me/submissions/b93865ad-d605-418c-977a-d52222db9a50

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_4f9da5bc_ae01_4349_bf9c_64dbf4d60dbc_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn U → T ≤ U → U = T)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by
  obtain ⟨U, hU, hTU, hEdges⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_4f9da5bc_ae01_4349_bf9c_64dbf4d60dbc_a1
      T hT hCard
  have hEq : U = T := hmax U hU hTU
  subst U
  omega