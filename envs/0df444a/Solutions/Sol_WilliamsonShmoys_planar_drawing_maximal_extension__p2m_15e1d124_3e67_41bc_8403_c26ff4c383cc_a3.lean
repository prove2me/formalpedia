-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_15e1d124_3e67_41bc_8403_c26ff4c383cc_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:18:37.159741+00:00
-- url     : https://prove2.me/submissions/9ae3e897-026f-4d5f-a573-57db24053371

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U) :
    ∃ M : SimpleGraph V,
      U ≤ M ∧ HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) ∧
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel M.Adj := Classical.decRel M.Adj
       U.edgeFinset.card ≤ M.edgeFinset.card) := by
  classical
  let S : Finset {G : SimpleGraph V // U ≤ G ∧ HasPlanarDrawingOn G} := Finset.univ
  have hS : S.Nonempty := by
    exact ⟨⟨U, le_rfl, hU⟩, by simp [S]⟩
  obtain ⟨m, hmS, hmax⟩ :=
    Finset.exists_max_image S (fun G => G.1.edgeFinset.card) hS
  refine ⟨m.1, m.2.1, m.2.2, ?_, ?_⟩
  · intro N hMN hN
    by_contra hNM
    have hlt : m.1 < N := lt_of_le_not_ge hMN hNM
    have hedge : m.1.edgeFinset ⊂ N.edgeFinset :=
      SimpleGraph.edgeFinset_strict_mono hlt
    have hcard : m.1.edgeFinset.card < N.edgeFinset.card :=
      Finset.card_lt_card hedge
    have hmaxN := hmax ⟨N, m.2.1.trans hMN, hN⟩ (by simp [S])
    exact (not_le_of_gt hcard) hmaxN
  · have hbase := hmax ⟨U, le_rfl, hU⟩ (by simp [S])
    simpa [SimpleGraph.edgeFinset] using hbase