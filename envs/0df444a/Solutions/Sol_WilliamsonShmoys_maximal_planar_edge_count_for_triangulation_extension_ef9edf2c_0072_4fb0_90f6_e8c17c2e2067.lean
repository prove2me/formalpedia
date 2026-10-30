-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:47:28.242414+00:00
-- url     : https://prove2.me/submissions/0e977aa0-4af2-4e5f-bcee-9ddf3cc5e60f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKD, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_triangulation_extension H hV hH
  have hKH : K = H := hmax K hHK hKD
  have heq : K.edgeSet.ncard = H.edgeSet.ncard :=
    congrArg (fun G : SimpleGraph V => G.edgeSet.ncard) hKH
  omega