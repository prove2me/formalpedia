-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph_of_connected_drawing__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:02:56.435936+00:00
-- url     : https://prove2.me/submissions/868ee5bc-fbf9-47f5-8336-efc8abb313aa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_predicate_has_maximal_extension__p2m_90a1d3cf_69db_4650_95dd_fb78166e4c20_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) (hconn : M.Connected) :
    ∃ N : SimpleGraph V, M <= N ∧ N.Connected ∧ HasPlanarDrawingOn N ∧
      (∀ K : SimpleGraph V, N <= K -> HasPlanarDrawingOn K -> K = N) := by
  let S : SimpleGraph V -> Prop := fun G => M <= G ∧ HasPlanarDrawingOn G
  have hSM : S M := ⟨le_rfl, hM⟩
  obtain ⟨N, hSN, hmax⟩ :=
    WilliamsonShmoys.finite_predicate_has_maximal_extension__p2m_90a1d3cf_69db_4650_95dd_fb78166e4c20_a1
      S M hSM
  rcases hSN with ⟨hMN, hNdraw⟩
  refine ⟨N, hMN, hconn.mono hMN, hNdraw, ?_⟩
  intro K hNK hKdraw
  exact hmax K hNK ⟨hMN.trans hNK, hKdraw⟩