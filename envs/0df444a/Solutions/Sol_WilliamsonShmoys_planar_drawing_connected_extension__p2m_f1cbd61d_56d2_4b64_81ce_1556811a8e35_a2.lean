-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:09:00.023942+00:00
-- url     : https://prove2.me/submissions/2f73691f-230a-4323-bf24-40fc4c5a1dc4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_8e16201b_1194_4bde_8c0d_f203800a8dc6_a1
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_strict_extension__p2m_8e16201b_1194_4bde_8c0d_f203800a8dc6_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : Nat.le 3 (Fintype.card V)) :
    Exists fun (H : SimpleGraph V) =>
      Exists fun (dH : DecidableRel H.Adj) =>
        And H.Connected
          (And (WilliamsonShmoys.HasPlanarDrawingOn H)
            (Nat.le K.edgeFinset.card H.edgeFinset.card)) := by
  classical
  obtain ⟨H, dH, hKH, hH, hCard, hMax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_8e16201b_1194_4bde_8c0d_f203800a8dc6_a1 K dK hK
  have hConnected : H.Connected := by
    by_contra hNotConnected
    obtain ⟨J, dJ, hHJ, hNe, hJ⟩ :=
      WilliamsonShmoys.planar_disconnected_strict_extension__p2m_8e16201b_1194_4bde_8c0d_f203800a8dc6_a1 H dH hH hNotConnected hn
    have hKJ : K ≤ J := le_trans hKH hHJ
    have hJeq : J = H := hMax J dJ hKJ hJ hHJ
    exact hNe hJeq.symm
  exact ⟨H, dH, hConnected, hH, hCard⟩