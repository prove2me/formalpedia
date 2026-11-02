-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:19:59.189355+00:00
-- url     : https://prove2.me/submissions/af10cbe4-9bc2-4819-a980-7d11a3229ad4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_connected__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_le_of_le__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun (H : SimpleGraph V) =>
      Exists fun (dH : DecidableRel H.Adj) =>
        And H.Connected
          (And (WilliamsonShmoys.HasPlanarDrawingOn H)
            (Nat.le K.edgeFinset.card H.edgeFinset.card)) := by
  classical
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2 K hK
  have hconn : H.Connected :=
    WilliamsonShmoys.maximal_planar_extension_connected__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2
      K H hH hKH hmax
  let dH : DecidableRel H.Adj := Classical.decRel _
  letI : DecidableRel K.Adj := dK
  letI : DecidableRel H.Adj := dH
  have hcount : Nat.le K.edgeFinset.card H.edgeFinset.card :=
    WilliamsonShmoys.edgeFinset_card_le_of_le__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2 K H hKH
  exact ⟨H, dH, hconn, hH, hcount⟩