-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_7aa49e78_992e_47a4_a47f_24fc3e2cd1e1_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:06:40.323414+00:00
-- url     : https://prove2.me/submissions/09972648-9205-4b23-a5d4-4e083db0a422

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edgeFinset_maximal_of_nonempty_predicate__p2m_adc3d123_0e13_438c_852d_da6c76884acd_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ G : SimpleGraph V,
      K.edgeFinset ⊆ G.edgeFinset ∧
      HasPlanarDrawingOn G ∧
      ∀ H : SimpleGraph V,
        G.edgeFinset ⊆ H.edgeFinset →
        HasPlanarDrawingOn H →
        H.edgeFinset ⊆ G.edgeFinset := by
  classical
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  let P : SimpleGraph V → Prop := fun G =>
    K.edgeFinset ⊆ G.edgeFinset ∧ HasPlanarDrawingOn G
  have hP : ∃ G, P G := ⟨K, Finset.Subset.rfl, hK⟩
  obtain ⟨G, hPG, hmax⟩ :=
    WilliamsonShmoys.exists_edgeFinset_maximal_of_nonempty_predicate__p2m_adc3d123_0e13_438c_852d_da6c76884acd_a2
      P hP
  refine ⟨G, hPG.1, hPG.2, ?_⟩
  intro H hGH hH
  apply hmax H hGH
  exact ⟨Finset.Subset.trans hPG.1 hGH, hH⟩