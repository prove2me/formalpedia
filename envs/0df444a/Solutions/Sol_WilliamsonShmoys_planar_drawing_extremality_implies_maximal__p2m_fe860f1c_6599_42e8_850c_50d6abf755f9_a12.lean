-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extremality_implies_maximal__p2m_fe860f1c_6599_42e8_850c_50d6abf755f9_a12
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:42:19.029587+00:00
-- url     : https://prove2.me/submissions/7aa5bdb1-b683-445b-aba1-dd1d300b9ccc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_85dfe40e_bf21_4653_aec5_d5293b86ee0f_a2
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    ∀ M : SimpleGraph V, H ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = H := by
  intro M hHM hM
  by_contra hne
  have hsub : H.edgeSet ⊆ M.edgeSet := SimpleGraph.edgeSet_mono hHM
  have hedges : H.edgeSet ≠ M.edgeSet := by
    intro heq
    apply hne
    exact (SimpleGraph.edgeSet_inj).mp heq.symm
  have hproper : H.edgeSet ⊂ M.edgeSet :=
    Set.ssubset_iff_subset_ne.mpr ⟨hsub, hedges⟩
  have hlt : H.edgeSet.ncard < M.edgeSet.ncard := Set.ncard_lt_ncard hproper
  have hbound := WilliamsonShmoys.planar_drawing_edge_bound__p2m_85dfe40e_bf21_4653_aec5_d5293b86ee0f_a2 M hM hV
  omega