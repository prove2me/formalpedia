-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_connected_augmentation__p2m_9e7a5396_2787_4caf_938c_608408887b08_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:34:25.013804+00:00
-- url     : https://prove2.me/submissions/9d4dbe36-836c-4f35-94b2-0b05576b408d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_strict_subgraph_edgeSet_ncard__p2m_8470bdfe_f75c_45f2_9449_e6bb0fb08f8f_a1
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_connected_supergraph__p2m_8470bdfe_f75c_45f2_9449_e6bb0fb08f8f_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ H.Connected) :
    ∃ H' : SimpleGraph V,
      HasPlanarDrawingOn H' ∧ H'.Connected ∧
      H.edgeSet.ncard + 1 ≤ H'.edgeSet.ncard := by
  obtain ⟨H', hsub, hne, hplanar', hconnected'⟩ :=
    WilliamsonShmoys.disconnected_planar_connected_supergraph__p2m_8470bdfe_f75c_45f2_9449_e6bb0fb08f8f_a1
      H hplanar hV hdisconnected
  have hcard : H.edgeSet.ncard < H'.edgeSet.ncard :=
    WilliamsonShmoys.strict_subgraph_edgeSet_ncard__p2m_8470bdfe_f75c_45f2_9449_e6bb0fb08f8f_a1
      H H' hsub hne.symm
  exact ⟨H', hplanar', hconnected', Nat.succ_le_of_lt hcard⟩