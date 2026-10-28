-- Prove2me | solution 1 for WilliamsonShmoys.drawable_disconnected_has_strict_planar_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:06:40.233473+00:00
-- url     : https://prove2.me/submissions/63e92d08-3c62-4be6-b1a3-00c8db252476
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_separating_cut_of_not_connected
import Theorems.Thm_WilliamsonShmoys_planar_cut_edge_extension

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by
  obtain ⟨A, hA, hAc, hCut⟩ :=
    WilliamsonShmoys.exists_separating_cut_of_not_connected K hCard hDisconnected
  obtain ⟨u, hu⟩ := hA
  obtain ⟨v, hv⟩ := hAc
  have hv' : v ∉ A := by simpa using hv
  exact WilliamsonShmoys.planar_cut_edge_extension K hK A hCut u v hu hv'