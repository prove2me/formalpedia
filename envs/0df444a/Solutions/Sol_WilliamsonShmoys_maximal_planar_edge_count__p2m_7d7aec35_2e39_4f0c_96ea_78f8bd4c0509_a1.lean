-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_7d7aec35_2e39_4f0c_96ea_78f8bd4c0509_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:31:35.544048+00:00
-- url     : https://prove2.me/submissions/d85d654d-5736-4dd4-87fb-38de2948c4a7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_513f0e25_8b21_45bc_8db8_f06f4ba42a04_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation__p2m_513f0e25_8b21_45bc_8db8_f06f4ba42a04_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  have hUpper := WilliamsonShmoys.planar_edge_upper_bound__p2m_513f0e25_8b21_45bc_8db8_f06f4ba42a04_a1
    L hL hCard
  by_contra hne
  have hGap : L.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨M, hLM, hneq, hDrawM⟩ :=
    WilliamsonShmoys.planar_edge_augmentation__p2m_513f0e25_8b21_45bc_8db8_f06f4ba42a04_a1
      L hL hCard hGap
  exact hneq (hMax M hLM hDrawM)