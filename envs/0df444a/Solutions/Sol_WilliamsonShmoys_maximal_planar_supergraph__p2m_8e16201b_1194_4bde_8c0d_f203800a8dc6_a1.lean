-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_8e16201b_1194_4bde_8c0d_f203800a8dc6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:22:14.125736+00:00
-- url     : https://prove2.me/submissions/2b69023a-d580-48d2-989d-e3c64f6c9ddc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_57a6043d_0c29_4d4d_8b4a_350055d97afc_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun (H : SimpleGraph V) =>
      Exists fun (dH : DecidableRel H.Adj) =>
        And (K ≤ H)
          (And (WilliamsonShmoys.HasPlanarDrawingOn H)
            (And (Nat.le K.edgeFinset.card H.edgeFinset.card)
              (∀ (J : SimpleGraph V), ∀ (dJ : DecidableRel J.Adj),
                K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J →
                  H ≤ J → J = H))) := by
  classical
  obtain ⟨H, dH, hKH, hH, hcard, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_supergraph__p2m_57a6043d_0c29_4d4d_8b4a_350055d97afc_a1
      K dK WilliamsonShmoys.HasPlanarDrawingOn hK
  exact ⟨H, dH, hKH, hH, hcard, fun J _ hKJ hJ hHJ =>
    hmax J hKJ hJ hHJ⟩