-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_connected__p2m_c5c73f75_8c1e_44ef_9deb_26150704a428_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:04:20.684106+00:00
-- url     : https://prove2.me/submissions/d833e379-bc9e-4787-850c-c24ea674d699
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_extension_adds_edge_of_not_connected__p2m_28f50d30_117d_4a63_8d20_afb26b4b003d_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall J : SimpleGraph V, H <= J ->
      WilliamsonShmoys.HasPlanarDrawingOn J -> H = J) :
    H.Connected := by
  by_contra hconn
  obtain ⟨J, hsub, hneq, hJ⟩ :=
    WilliamsonShmoys.planar_extension_adds_edge_of_not_connected__p2m_28f50d30_117d_4a63_8d20_afb26b4b003d_a1
      H hcard hH hconn
  exact hneq (hmax J hsub hJ)