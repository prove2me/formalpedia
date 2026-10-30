-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_extension_of_strict_extension__p2m_5b4ba625_e76a_490b_a06e_75a37c9ee7a0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:15:16.857205+00:00
-- url     : https://prove2.me/submissions/a9c6e222-da11-45c0-9fa8-85831597051c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_e59f08ac_c69e_4607_8c7d_4507b335dcb0_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V)
    (extend : forall (G : SimpleGraph V), HasPlanarDrawingOn G -> Not G.Connected ->
      Exists fun K : SimpleGraph V => And (LE.le G K) (And (Not (G = K)) (HasPlanarDrawingOn K))) :
    Exists fun K : SimpleGraph V => And (LE.le H K) (And K.Connected (HasPlanarDrawingOn K)) := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_e59f08ac_c69e_4607_8c7d_4507b335dcb0_a1 H hH
  refine ⟨K, hHK, ?_, hK⟩
  by_contra hconn
  obtain ⟨L, hKL, hne, hL⟩ := extend K hK hconn
  have hLK : L = K := hmax L hKL hL
  exact hne hLK.symm