-- Prove2me | solution 1 for WilliamsonShmoys.exists_connected_supergraph_of_bridge_extension__p2m_5d530b65_2a84_4113_95c6_4b4a03a3063e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:18:33.210973+00:00
-- url     : https://prove2.me/submissions/89b085f3-22aa-4e18-8312-ff1739cb31df
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_bridge_extension_strict_edgeSet__p2m_1743449e_70b2_453d_82e4_df1f7d1e75bd_a3
import Theorems.Thm_WilliamsonShmoys_finite_graph_maximal_extension__p2m_1743449e_70b2_453d_82e4_df1f7d1e75bd_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P G)
    (hstep : ∀ (K : SimpleGraph V),
      G.edgeSet ⊆ K.edgeSet →
      P K →
      ¬ K.Connected →
      ∃ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet ∧
        (∃ u v, ¬ K.Reachable u v ∧ L.Adj u v) ∧
        P L) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧ H.Connected ∧ P H := by
  obtain ⟨H, hGH, hPH, hconn⟩ :=
    WilliamsonShmoys.finite_graph_maximal_extension__p2m_1743449e_70b2_453d_82e4_df1f7d1e75bd_a3
      G P hP (by
        intro K hGK hPK hdisc
        obtain ⟨L, hKL, hbridge, hPL⟩ := hstep K hGK hPK hdisc
        rcases hbridge with ⟨u, v, hreach, hadj⟩
        exact ⟨L,
          WilliamsonShmoys.bridge_extension_strict_edgeSet__p2m_1743449e_70b2_453d_82e4_df1f7d1e75bd_a3
            hKL hreach hadj,
          hPL⟩)
  exact ⟨H, hGH, hconn, hPH⟩