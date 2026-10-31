-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_extension__p2m_3e4841aa_5cc8_43c5_ada3_9b4132733a6e_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:43:11.678612+00:00
-- url     : https://prove2.me/submissions/f842d078-307c-4c6b-81f3-d523b8e14621
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_by_bridging_components__p2m_9d6795a0_df2a_4cd4_b626_1874c3a84ac3_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hconn : ¬ L.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, L ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ ¬ H ≤ L := by
  have hV2 : 2 ≤ Fintype.card V := le_trans (by decide) hV
  obtain ⟨H, hLH, hH, hnew⟩ :=
    WilliamsonShmoys.planar_extension_by_bridging_components__p2m_9d6795a0_df2a_4cd4_b626_1874c3a84ac3_a1
      L hL hconn hV2
  refine ⟨H, hLH, hH, ?_⟩
  intro hHL
  obtain ⟨u, v, hHad, hLnot⟩ := hnew
  exact hLnot (hHL hHad)