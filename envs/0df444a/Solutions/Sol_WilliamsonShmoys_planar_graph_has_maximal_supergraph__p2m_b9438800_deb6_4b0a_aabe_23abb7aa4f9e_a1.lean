-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_maximal_supergraph__p2m_b9438800_deb6_4b0a_aabe_23abb7aa4f9e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:47:13.018437+00:00
-- url     : https://prove2.me/submissions/eccd5f84-ab3c-423c-a46c-d35fa52d698a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by
  classical
  let S : Set (SimpleGraph V) := {M | L ≤ M ∧ HasPlanarDrawingOn M}
  have hS : S.Nonempty := by
    refine ⟨L, ?_⟩
    simp [S, hL]
  have hSf : S.Finite := Set.toFinite S
  obtain ⟨M, hM, hmax⟩ := hSf.exists_maximal hS
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro N hMN hN
  exact hmax ⟨hM.1.trans hMN, hN⟩ hMN