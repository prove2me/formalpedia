-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_05250361_edf9_4bba_b0bb_f1c9e6abc2aa
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T01:42:34.999908+00:00
-- url     : https://prove2.me/submissions/d8166314-edce-4efd-8b47-c45d484bc361

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5
import Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeSet_ncard_mono_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ Q : SimpleGraph V,
      (∀ {u v : V}, M.Adj u v → Q.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      (M.edgeSet.ncard : Int) ≤ (Q.edgeSet.ncard : Int) ∧
      (Q.edgeSet.ncard : Int) =
        (3 : Int) * (Fintype.card V : Int) - 6 := by
  obtain ⟨Q, hMQ, hQ, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5
      M hV hM
  have hcard : (M.edgeSet.ncard : Int) ≤ (Q.edgeSet.ncard : Int) :=
    WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5
      M Q hMQ
  have hcount : (Q.edgeSet.ncard : Int) =
      (3 : Int) * (Fintype.card V : Int) - 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5
      Q hV hQ hmax
  exact ⟨Q, hMQ, hQ, hcard, hcount⟩